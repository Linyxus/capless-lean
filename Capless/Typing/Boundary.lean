import Capless.Typing
import Capless.Weakening.Typing
import Capless.Narrowing.Typing
namespace Capless

/-!
The following proves a substitution theorem specialised to the typing of boundary bodies.
It is a prerequisite for the (ENTER) case in the preservation theorem.
!-/

def VarRename.boundary {Γ : Context n m k} {S : SType n m k} :
  VarMap
    ((Γ,c:CapSet),x:(Label[S.cweaken])^{c=0})
    FinFun.weaken.ext
    (((Γ.label S),c:CapSet),x:(Label[S.weaken.cweaken])^{c=0}) := by
  constructor
  case map =>
    intro x E hb
    cases hb
    case here =>
      simp [FinFun.weaken, FinFun.ext]
      rw [<- CType.weaken_rename]
      simp [CType.rename, SType.rename]
      rw [SType.cweaken_rename_comm]
      constructor
    case there_var hb0 =>
      cases hb0
      case there_cvar hb0 =>
        rw [<- CType.weaken_rename]
        simp [FinFun.weaken, FinFun.ext]
        constructor
        rw [CType.cweaken_rename_comm]
        constructor
        constructor; easy
  case tmap =>
    intro X b hb
    cases hb; rename_i hb
    cases hb; rename_i hb
    rw [<- TBinding.weaken_rename]
    rw [TBinding.cweaken_rename_comm]
    constructor; constructor; constructor; easy
  case cmap =>
    intro c b hb
    cases hb; rename_i hb
    cases hb
    case here =>
      rw [<- CBinding.weaken_rename]
      rw [CBinding.cweaken_rename_comm]
      constructor; constructor
    case there_cvar hb =>
      rw [<- CBinding.weaken_rename]
      rw [CBinding.cweaken_rename_comm]
      constructor; constructor
      constructor; easy
  case lmap =>
    intro x S hb
    cases hb; rename_i hb
    cases hb; rename_i hb
    simp [FinFun.weaken, FinFun.ext]
    rw [<- SType.weaken_rename]
    rw [SType.cweaken_rename_comm]
    constructor; constructor; constructor; easy

def CVarRename.boundary {Γ : Context n m k} {S : SType n m k} :
  CVarMap
    (((Γ.label S),c:CapSet),x:(Label[S.weaken.cweaken])^{c=0})
    FinFun.weaken.ext
    ((((Γ.label S),c:={x=0}),c:CapSet),x:(Label[S.weaken.cweaken.cweaken])^{c=0}) := by
  constructor
  case map =>
    intro x T hb
    cases hb
    case here =>
      rw [<- CType.weaken_crename]
      simp [CType.crename, SType.crename, FinFun.ext]
      rw [<- SType.cweaken_crename]
      constructor
    case there_var hb0 =>
      cases hb0; rename_i hb0
      cases hb0; rename_i hb0
      rw [<- CType.weaken_crename]
      rw [<- CType.cweaken_crename]
      repeat constructor
      easy
  case tmap =>
    intro X b hb
    cases hb; rename_i hb
    cases hb; rename_i hb
    cases hb; rename_i hb
    rw [<- TBinding.weaken_crename]
    rw [<- TBinding.cweaken_crename]
    repeat constructor
    easy
  case cmap =>
    intro c b hb
    cases hb; rename_i hb
    cases hb
    case here =>
      simp [FinFun.ext]
      rw [<- CBinding.weaken_crename]
      constructor; constructor
    case there_cvar hb =>
      cases hb; rename_i hb
      rw [<- CBinding.weaken_crename]
      rw [<- CBinding.cweaken_crename]
      simp [FinFun.weaken, FinFun.ext]
      repeat constructor
      easy
  case lmap =>
    intro l S hb
    cases hb; rename_i hb
    cases hb; rename_i hb
    cases hb
    case here =>
      rw [<- SType.weaken_crename]
      rw [<- SType.cweaken_crename]
      repeat constructor
    case there_label hb =>
      rw [<- SType.weaken_crename]
      rw [<- SType.cweaken_crename]
      repeat constructor
      easy

theorem SType.cweaken_copen_id {S : SType n m k} :
  S.cweaken.crename (FinFun.open x) = S := by
  simp [SType.cweaken, SType.crename_crename]
  simp [FinFun.open_comp_weaken, SType.crename_id]

theorem CType.cweaken_copen_id {T : CType n m k} :
  T.cweaken.crename (FinFun.open x) = T := by
  simp [CType.cweaken, CType.crename_crename]
  simp [FinFun.open_comp_weaken, CType.crename_id]

theorem TBinding.cweaken_copen_id {b : TBinding n m k} :
  b.cweaken.crename (FinFun.open x) = b := by
  simp [TBinding.cweaken, TBinding.crename_crename]
  simp [FinFun.open_comp_weaken, TBinding.crename_id]

def CVarSubst.boundary {Γ : Context n m k} {S : SType n m k} :
  CVarSubst
    ((((Γ.label S),c:={x=0}),c:CapSet),x:(Label[S.weaken.cweaken.cweaken])^{c=0})
    (FinFun.open 0)
    (((Γ.label S),c:={x=0}),x:(Label[S.weaken.cweaken])^{c=0}) := by
  constructor
  case map =>
    intro x T hb
    cases hb
    case here =>
      rw [<- CType.weaken_crename]
      simp [CType.crename, SType.crename, FinFun.open]
      simp [SType.cweaken_copen_id]
      constructor
    case there_var hb0 =>
      cases hb0; rename_i hb0
      cases hb0; rename_i hb0
      cases hb0; rename_i hb0
      rw [<- CType.weaken_crename]
      simp [CType.cweaken_copen_id]
      repeat constructor
      easy
  case tmap =>
    intro X b hb
    cases hb; rename_i hb
    cases hb; rename_i hb
    cases hb; rename_i hb
    cases hb; rename_i hb
    rw [<- TBinding.weaken_crename]
    simp [TBinding.cweaken_copen_id]
    repeat constructor
    easy
  case cmap =>
    intro c b hb
    sorry
  case lmap =>
    intro l S hb
    cases hb; rename_i hb
    cases hb; rename_i hb
    cases hb; rename_i hb
    cases hb
    case here =>
      rw [<- SType.weaken_crename]
      rw [SType.cweaken_copen_id]
      repeat constructor
    case there_label hb =>
      rw [<- SType.weaken_crename]
      rw [SType.cweaken_copen_id]
      repeat constructor
      easy

theorem Term.copen_cweaken_ext {t : Term n m (k+1)} :
  (t.crename (FinFun.weaken.ext)).crename (FinFun.open 0) = t := by
  simp [Term.crename_crename]
  simp [FinFun.open_zero_comp_weaken_ext]
  simp [Term.crename_id]

theorem EType.copen_cweaken_ext {E : EType n m (k+1)} :
  (E.crename (FinFun.weaken.ext)).crename (FinFun.open 0) = E := by
  simp [EType.crename, EType.crename_crename]
  simp [FinFun.open_zero_comp_weaken_ext]
  simp [EType.crename_id]

theorem CaptureSet.copen_cweaken_ext {C : CaptureSet n (k+1)} :
  (C.crename (FinFun.weaken.ext)).crename (FinFun.open 0) = C := by
  simp [CaptureSet.crename, CaptureSet.crename_crename]
  simp [FinFun.open_zero_comp_weaken_ext]
  simp [CaptureSet.crename_id]

theorem Typed.boundary_body_typing {Γ : Context n m k} {S : SType n m k}
  (ht : Typed ((Γ,c:CapSet),x:(Label[S.cweaken])^{c=0}) t E Ct) :
  Typed ((Γ.label S),c:={x=0}) t E Ct := by
  have h := ht.rename VarRename.boundary
  have h := h.crename CVarRename.boundary
  have h := h.csubst CVarSubst.boundary
  simp [Term.copen_cweaken_ext, EType.copen_cweaken_ext, CaptureSet.copen_cweaken_ext] at h
  sorry

end Capless
