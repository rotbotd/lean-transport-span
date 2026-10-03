import TransportSpan

namespace TransportSpan.Demo

universe u

def vectorCast {α : Type u} {n m : Nat}
    (eq : n = m) (xs : Vector α n) : Vector α m :=
  transport { Vector α n -> Vector α m } eq xs

theorem firstOccurrence {α : Type u} (R : α → α → Prop)
    {a b : α} (eq : a = b) (x : R a a) : R b a :=
  transport { R a a -> R b a } eq x

theorem secondOccurrence {α : Type u} (R : α → α → Prop)
    {a b : α} (eq : a = b) (x : R a a) : R a b :=
  transport { R a a -> R a b } eq x

theorem bothOccurrences {α : Type u} (R : α → α → Prop)
    {a b : α} (eq : a = b) (x : R a a) : R b b :=
  transport { R a a -> R b b } eq x

theorem underForall {α β : Type u} (R : α → β → Prop)
    {a b : α} (eq : a = b) (x : ∀ y, R a y) : ∀ y, R b y :=
  transport { (∀ y, R a y) -> (∀ y, R b y) } eq x

def underFunctionType {α β : Type u} (F : α → Type u)
    {a b : α} (eq : a = b) (x : β → F a) : β → F b :=
  transport { (β → F a) -> (β → F b) } eq x

theorem dependentDomain (P : (n : Nat) → Fin n → Prop)
    {n m : Nat} (eq : n = m) (x : ∀ i : Fin n, P n i) :
    ∀ i : Fin m, P m i :=
  transport {
    (∀ i : Fin n, P n i) ->
    (∀ i : Fin m, P m i)
  } eq x

-- The span rejects a dishonest destination before the kernel sees a term.
/--
error: the displayed endpoint types differ somewhere not justified by the equality
source fragment:
  a
target fragment:
  c
-/
#guard_msgs (error) in
example {α : Type u} {a b c : α} (P : α → Prop)
    (eq : a = b) (x : P a) : P c :=
  transport { P a -> P c } eq x

end TransportSpan.Demo
