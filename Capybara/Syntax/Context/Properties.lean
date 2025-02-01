import Capless.Tactics
import Capybara.Syntax.Context.Core
namespace Capybara

theorem TBinding.rename_id {B : TBinding n m k} : B.rename Renaming.id = B := by
  cases B
  case param => simp [TBinding.rename, SType.rename_id]
  case typealias => simp [TBinding.rename, SType.rename_id]

theorem TBinding.rename_weaken {B : TBinding n m k} :
  (B.rename ρ).weaken = B.weaken.rename ρ.ext := by
  cases B
  case param =>
    simp [TBinding.weaken, TBinding.rename]
    apply SType.rename_weaken
  case typealias =>
    simp [TBinding.weaken, TBinding.rename]
    apply SType.rename_weaken

theorem TBinding.rename_tweaken {B : TBinding n m k} :
  (B.rename ρ).tweaken = B.tweaken.rename ρ.text := by
  cases B
  case param =>
    simp [TBinding.tweaken, TBinding.rename]
    apply SType.rename_tweaken
  case typealias =>
    simp [TBinding.tweaken, TBinding.rename]
    apply SType.rename_tweaken

theorem TBinding.rename_cweaken {B : TBinding n m k} :
  (B.rename ρ).cweaken = B.cweaken.rename ρ.cext := by
  cases B
  case param =>
    simp [TBinding.cweaken, TBinding.rename]
    apply SType.rename_cweaken
  case typealias =>
    simp [TBinding.cweaken, TBinding.rename]
    apply SType.rename_cweaken

theorem CBinding.rename_weaken {B : CBinding n k} {ρ : Renaming n m k n' m' k'} :
  (B.rename ρ.asCapt).weaken = B.weaken.rename ρ.ext.asCapt := by
  cases B
  case param K =>
    simp [CBinding.weaken, CBinding.rename]
    cases K
    case Sep D =>
      cases D; simp [CKind.rename]; simp [SepDegree.rename]
      apply CaptureSet.rename_weaken
    case Fresh =>
      simp [CKind.rename]
  case capturealias C =>
    simp [CBinding.weaken, CBinding.rename]
    simp [CaptureSet.rename_comp]
    rw [Renaming.weaken_transportM (m1:=0) (m2:=m')]
    rw [<-Renaming.comp_asCapt]
    rw [Renaming.weaken_transportM (m1:=0) (m2:=m)]
    rw [<-Renaming.comp_asCapt]
    simp [Renaming.comp_weaken]

theorem CBinding.rename_cweaken {B : CBinding n k} {ρ : Renaming n m k n' m' k'} :
  (B.rename ρ.asCapt).cweaken = B.cweaken.rename ρ.cext.asCapt := by
  cases B
  case param K =>
    simp [CBinding.cweaken, CBinding.rename]
    cases K
    case Sep D =>
      cases D; simp [CKind.rename]; simp [SepDegree.rename]
      apply CaptureSet.rename_cweaken
    case Fresh =>
      simp [CKind.rename]
  case capturealias C =>
    simp [CBinding.cweaken]; simp [CBinding.rename]
    apply CaptureSet.rename_cweaken

theorem Context.var_lookupc_inv {Γ : Context n m k}
  (hb : (Γ,x:T).LookupC c B) :
  ∃ B0, Γ.LookupC c B0 ∧ B = B0.weaken := by cases hb; aesop

theorem Context.var_lookupc_fresh_inv {Γ : Context n m k}
  (hb : (Γ,x:T).LookupC c (CBinding.param CKind.Fresh)) :
  Γ.LookupC c (CBinding.param CKind.Fresh) := by
  have ⟨B0, hb0, heq⟩ := Context.var_lookupc_inv hb
  cases B0 <;> try cases heq
  rename_i K; cases K <;> try cases heq
  easy

theorem Context.tvar_lookupc_inv {Γ : Context n m k}
  (hb : (Γ,X:S).LookupC c B) :
  Γ.LookupC c B := by cases hb; aesop

theorem Context.cvar_lookupc_inv {Γ : Context n m k}
  (hb : (Γ,c:K).LookupC c B) :
  (c = 0 ∧ B = K.cweaken) ∨
  (∃ c0 B0, Γ.LookupC c0 B0 ∧ c = c0.succ ∧ B = B0.cweaken) := by
  cases hb
  case here => apply Or.inl; aesop
  case cthere hb0 => apply Or.inr; aesop

end Capybara
