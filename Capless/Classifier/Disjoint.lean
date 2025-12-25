import Capless.Classifier.Kind
import Capless.Classifier.Intersection
import Capless.Classifier.Semantics

namespace Capless

/-- Two subtrees are disjoint if they do not share any common nodes. -/
inductive Kind.Disjoint : Kind -> Kind -> Prop where
  | intersect : Intersect K L R -> R.IsEmpty -> Disjoint K L

/-- Decides whether two Kinds are disjoint. -/
def Kind.disjoint (a b : Kind) :=  (IsEmpty.decidable (K:=a.intersect b)).decide

theorem Kind.Disjoint.empty_intersect : IsEmpty (K.intersect L) ↔ Disjoint K L := by
  apply Iff.intro <;> intro h
  . apply intersect (Intersect.lawful _ _) h
  . cases h
    rename_i h1 h2
    rw [← SEmpty.is_empty] at *
    intro c hc
    have hi' := Intersect.lawful K L
    have ⟨_, _⟩ := hi'.contains_inv hc
    apply h2 c
    apply! h1.contains

/-- Proves that `disjoint` follows derivation. -/
theorem Kind.disjoint.lawful : Disjoint K L ↔ disjoint K L := by
  rw [disjoint, decide_eq_true_iff]
  exact Disjoint.empty_intersect.symm

theorem Kind.disjoint.symm (hs : disjoint K L) : disjoint L K := by
  rw [← lawful] at *
  cases hs
  rename_i h1 h2
  have h := Intersect.lawful L K
  apply Disjoint.intersect h
  rw [← SEmpty.is_empty] at *
  intro c hc
  apply h2 c
  have ⟨_, _⟩ := h.contains_inv hc
  apply! h1.contains

end Capless
