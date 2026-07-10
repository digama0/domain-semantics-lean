import DomainSemantics
import Lean.Util.FoldConsts
import Lean.DeclarationRange

open Lean Elab Command

namespace FindUnused

variable (env : Environment) in
/-- Walk the full transitive closure of constant dependencies starting from the
roots. Unlike `Batteries.Tactic.ShowUnused`, we recurse into *every* unseen
constant rather than only those in a candidate set — otherwise auxiliary
constants outside the candidate set (e.g. the per-field aux defs generated
by structure-instance syntax) break the dependency chain and constants
reachable only through them are spuriously reported as unused. -/
private partial def visit (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  let rec visitExpr (e : Expr) : StateM NameSet Unit := e.getUsedConstants.forM visit
  match env.find? n with
  | some (ConstantInfo.axiomInfo v)  => visitExpr v.type
  | some (ConstantInfo.defnInfo v)   => visitExpr v.type *> visitExpr v.value
  | some (ConstantInfo.thmInfo v)    => visitExpr v.type *> visitExpr v.value
  | some (ConstantInfo.opaqueInfo v) => visitExpr v.type *> visitExpr v.value
  | some (ConstantInfo.quotInfo _)   => pure ()
  | some (ConstantInfo.ctorInfo v)   => visitExpr v.type
  | some (ConstantInfo.recInfo v)    => visitExpr v.type
  | some (ConstantInfo.inductInfo v) => visitExpr v.type *> v.ctors.forM visit
  | none                             => pure ()

/-- Heuristic: notation/syntax declarations have type `Lean.ParserDescr` or
`Lean.TrailingParserDescr`. Skip them so the report only contains theorems
and definitions. -/
def isParserDecl (ci : ConstantInfo) : Bool :=
  ci.type.isAppOf ``Lean.ParserDescr
    || ci.type.isAppOf ``Lean.TrailingParserDescr

/-- Collect all non-internal declarations in modules under the given namespace
prefix. -/
def collectProjectDecls (env : Environment) (pfx : Name) : NameSet := Id.run do
  let mut decls : NameSet := {}
  for pair in env.constants.map₁.toList do
    let n := pair.1
    let ci := pair.2
    if n.isInternalDetail then continue
    if isParserDecl ci then continue
    let some idx := env.getModuleIdxFor? n | continue
    let some modName := env.header.moduleNames[idx.toNat]? | continue
    unless pfx.isPrefixOf modName do continue
    decls := decls.insert n
  return decls

def findUnused (pfx : Name) (outFile : System.FilePath) (roots : Array Name) :
    CommandElabM Unit := do
  let env ← getEnv
  for root in roots do
    unless env.contains root do
      throwError "root declaration {root} not found in environment"
  let candidates := collectProjectDecls env pfx
  let visited := ((roots.forM (visit env)).run {}).2
  let mut entries : Array (String × Nat × Name) := #[]
  for c in candidates do
    if visited.contains c then continue
    let some idx := env.getModuleIdxFor? c | continue
    let some modName := env.header.moduleNames[idx.toNat]? | continue
    -- Only report user-written declarations (those with a source range)
    let some r := declRangeExt.find? env c | continue
    let baseName := modName.components.getLast?.map toString |>.getD modName.toString
    entries := entries.push (s!"{baseName}.lean", r.range.pos.line, c)
  let sorted := entries.qsort fun a b =>
    if a.1 != b.1 then a.1 < b.1
    else a.2.1 < b.2.1
  let lines := sorted.toList.map fun (file, line, name) =>
    s!"{file}:{line}: {name}"
  IO.FS.writeFile outFile (String.intercalate "\n" lines ++ "\n")
  logInfo s!"Wrote {sorted.size} unused declarations to {outFile}"

end FindUnused

open DomainSemantics
run_cmd FindUnused.findUnused `DomainSemantics "unused.txt"  #[
  ``IsDefEq.iff, ``forallE_inv', ``sort_inv', ``sort_forallE_inv']
