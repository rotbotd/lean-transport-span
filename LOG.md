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

## 2026-10-03 — first downstream use

- Published the library at
  `https://github.com/rotbotd/lean-transport-span`; the PPA formalization pins
  commit `c415425` as its first external consumer.
- The fixed-point induction transports membership from `f(other)` to `other`.
  Its reaching-definitions proof also exposed an elaboration edge: when an
  `if_pos` proof's type is inferred without an annotation, reduction can erase
  the conditional endpoint that the span is meant to display. An explicitly
  typed local equality retains it and elaborates normally.
