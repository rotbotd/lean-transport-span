# transport-span

A small Lean 4 library for visible, term-mode transport:

```lean
transport { P a -> P b } eq x
```

The brace block is a **span**, not a function type. It tells the reader and
the elaborator where the payload starts and where it must arrive. The
elaborator compares both endpoints against the equality, reconstructs the
one-variable family from their visible difference, and emits `congrArg`
followed by `Eq.mp`. Lean's unchanged kernel checks the result.

See `TransportSpan/Demo.lean` for first-, second-, and both-occurrence
transports.

For example, the last one elaborates to the same shape as:

```lean
Eq.mp (congrArg (fun span => R span span) eq) x
```

## Check

```console
lake build
nix flake check
```
