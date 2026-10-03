# Log

## 2026-10-03 — first vertical slice

- Chose `transport { source -> target } equality payload` so the source and
  target types remain visible rather than being reconstructed from a motive.
- Implemented it as a term elaborator with structural endpoint comparison.
  Changed occurrences become a single family parameter; unchanged fragments
  remain fixed. The emitted object is `Eq.mp (congrArg family equality)
  payload`, checked by the kernel.
- Added vector transport and separate first/second/both occurrence examples.
- Added a negative check for a displayed target not reached by the equality.
- Exact emitted-term audit:
  `firstOccurrence` produces `fun span => R span a`, while
  `bothOccurrences` produces `fun span => R span span`.

## 2026-10-03 — binder traversal

- Extended endpoint comparison through `forall`, lambda, and local-let
  expressions while preserving their bound-variable structure.
- Added universal-proposition and function-type transports. These ensure the
  displayed span can expose a changed index beneath a binder rather than
  forcing an explicit motive.
- Added a dependent-domain test from `∀ i : Fin n, P n i` to
  `∀ i : Fin m, P m i`. The printed kernel term reconstructs precisely
  `fun span => ∀ i : Fin span, P span i`, so traversal preserves the link
  between a binder's changing domain and uses of its bound variable.
