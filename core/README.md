# DomainSemantics (core)

A trimmed-down variant of [the main library](../README.md) covering just
the core type theory — a dependently-typed λ-calculus with Π-types and a
universe hierarchy, without the additional type formers (Σ, Nat, Id) of
the main development. Kept as a smaller reference point for the same
proof architecture.

See the [main README](../README.md) for build instructions, validation
notes, and file-map layout — they apply here modulo the trimmed set of
type formers. This directory is a separate Lake package, so building the
whole repo means running `lake build` at the top level and again inside
`core/`.
