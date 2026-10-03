import Lean

/-!
`transport {A -> B} h x` displays both endpoints of a type transport.

The elaborator checks `x : A`, reconstructs a one-variable family from the
visible `A -> B` difference and `h`, and returns the corresponding equality
transport term. No tactic syntax appears at the call site.
-/

open Lean Elab Term Meta

syntax (name := transportSpan) "transport" "{" term:26 " -> " term "}" term:arg term:arg : term

private partial def abstractSpan
    (source target lhs rhs hole : Expr) : MetaM (Expr × Bool) := do
  if (← isDefEqGuarded source lhs) && (← isDefEqGuarded target rhs) then
    return (hole, true)
  if ← isDefEqGuarded source target then
    return (source, false)
  match source, target with
  | .app sf sa, .app tf ta =>
      let (f, changedF) ← abstractSpan sf tf lhs rhs hole
      let (a, changedA) ← abstractSpan sa ta lhs rhs hole
      return (.app f a, changedF || changedA)
  | .mdata sm se, .mdata _ te =>
      let (e, changed) ← abstractSpan se te lhs rhs hole
      return (.mdata sm e, changed)
  | .proj sn si se, .proj tn ti te =>
      unless sn == tn && si == ti do
        throwError "the displayed endpoint types differ somewhere not justified by the equality"
      let (e, changed) ← abstractSpan se te lhs rhs hole
      return (.proj sn si e, changed)
  | .forallE name sDomain sBody sInfo,
      .forallE _ tDomain tBody tInfo =>
      unless sInfo == tInfo do
        throwError "the displayed endpoint binders have different binder annotations"
      let (domain, changedDomain) ←
        abstractSpan sDomain tDomain lhs rhs hole
      let (body, changedBody) ← abstractSpan sBody tBody lhs rhs hole
      return (.forallE name domain body sInfo, changedDomain || changedBody)
  | .lam name sDomain sBody sInfo, .lam _ tDomain tBody tInfo =>
      unless sInfo == tInfo do
        throwError "the displayed endpoint lambdas have different binder annotations"
      let (domain, changedDomain) ←
        abstractSpan sDomain tDomain lhs rhs hole
      let (body, changedBody) ← abstractSpan sBody tBody lhs rhs hole
      return (.lam name domain body sInfo, changedDomain || changedBody)
  | .letE name sType sValue sBody sNondep,
      .letE _ tType tValue tBody tNondep =>
      unless sNondep == tNondep do
        throwError "the displayed endpoint lets have incompatible dependency information"
      let (type, changedType) ← abstractSpan sType tType lhs rhs hole
      let (value, changedValue) ← abstractSpan sValue tValue lhs rhs hole
      let (body, changedBody) ← abstractSpan sBody tBody lhs rhs hole
      return (.letE name type value body sNondep,
        changedType || changedValue || changedBody)
  | _, _ =>
      throwError
        "the displayed endpoint types differ somewhere not justified by the equality\nsource fragment:\n  {source}\ntarget fragment:\n  {target}"

@[term_elab transportSpan]
def elabTransportSpan : TermElab := fun stx expectedType? => do
  match stx with
  | `(transport { $source:term -> $target:term } $eqProof:term $payload:term) =>
      let sourceType ← elabType source
      let targetType ← elabType target
      let payloadExpr ← elabTermEnsuringType payload (some sourceType)
      let eqExpr ← elabTerm eqProof none
      synthesizeSyntheticMVarsNoPostponing

      let eqExpr ← instantiateMVars eqExpr
      let eqType ← inferType eqExpr
      let some (carrier, lhs, rhs) ← matchEq? eqType
        | throwErrorAt eqProof "expected an equality proof, got\n  {eqType}"

      let sourceType ← instantiateMVars sourceType
      let targetType ← instantiateMVars targetType
      let transported ← withLocalDeclD `span carrier fun hole => do
        let (motiveBody, changed) ←
          abstractSpan sourceType targetType lhs rhs hole
        unless changed do
          throwErrorAt stx
            "the displayed span contains no source-to-target occurrence licensed by the equality"
        let motive ← mkLambdaFVars #[hole] motiveBody
        let typeEquality ← mkCongrArg motive eqExpr
        mkEqMP typeEquality payloadExpr

      let transportedType ← inferType transported
      unless ← isDefEq transportedType targetType do
        throwErrorAt target
          "transported payload has type\n  {transportedType}\nbut the displayed target is\n  {targetType}"

      if let some expectedType := expectedType? then
        unless ← isDefEq targetType expectedType do
          throwErrorAt stx
            "transport span produces\n  {targetType}\nbut the surrounding term expects\n  {expectedType}"
      return transported
  | _ => throwUnsupportedSyntax
