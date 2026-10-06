import Batteries.CodeAction
import Batteries.Tactic.SeqFocus

/-! # Generic prelude

The `simp` lemmas from batteries that the project wants on by default.
This file used to hold a grab-bag of `List` and closure lemmas; they
served the level-indexed lookup and its sublist characterisation, both
of which are gone. -/

open Std

attribute [simp] Option.bind_eq_some_iff List.filterMap_cons
