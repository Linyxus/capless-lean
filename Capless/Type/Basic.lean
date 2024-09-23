import Capless.Type.Core
import Capless.Type.Renaming
namespace Capless

mutual

theorem EType.crename_rename_comm (E : EType n m k) (f : FinFun n n') (g : FinFun k k') :
  (E.rename f).crename g = (E.crename g).rename f :=
  match E with
  | EType.ex T => by
    have ih := CType.crename_rename_comm T f g.ext
    simp [EType.rename, EType.crename, ih]
  | EType.type T => by
    have ih := CType.crename_rename_comm T f g
    simp [EType.rename, EType.crename, ih]

theorem CType.crename_rename_comm (C : CType n m k) (f : FinFun n n') (g : FinFun k k') :
  (C.rename f).crename g = (C.crename g).rename f :=
  match C with
  | CType.capt C S => by
    have ih1 := SType.crename_rename_comm S f g
    simp [CType.rename, CType.crename, ih1, CaptureSet.crename_rename_comm]

theorem SType.crename_rename_comm (S : SType n m k) (f : FinFun n n') (g : FinFun k k') :
  (S.rename f).crename g = (S.crename g).rename f :=
  match S with
  | SType.top => by simp [SType.rename, SType.crename]
  | SType.tvar X => by simp [SType.rename, SType.crename]
  | SType.forall E1 E2 => by
    have ih1 := CType.crename_rename_comm E1 f g
    have ih2 := EType.crename_rename_comm E2 f.ext g
    simp [SType.rename, SType.crename, ih1, ih2]
  | SType.tforall S E => by
    have ih1 := SType.crename_rename_comm S f g
    have ih2 := EType.crename_rename_comm E f g
    simp [SType.rename, SType.crename, ih1, ih2]
  | SType.cforall E => by
    have ih := EType.crename_rename_comm E f g.ext
    simp [SType.rename, SType.crename, ih]
  | SType.box T => by
    have ih := CType.crename_rename_comm T f g
    simp [SType.rename, SType.crename, ih]

end

theorem EType.cweaken_rename_comm {E : EType n m k} :
  E.cweaken.rename f = (E.rename f).cweaken := by
  simp [cweaken, crename_rename_comm]

theorem CType.cweaken_rename_comm {C : CType n m k} :
  C.cweaken.rename f = (C.rename f).cweaken := by
  simp [cweaken, crename_rename_comm]

theorem SType.copen_rename_comm {S : SType n m (k+1)} :
  (S.copen x).rename f = (S.rename f).copen x := by
  simp [copen, crename_rename_comm]

theorem CType.copen_rename_comm {C : CType n m (k+1)} :
  (C.copen x).rename f = (C.rename f).copen x := by
  simp [copen, crename_rename_comm]

mutual

theorem EType.rename_rename (E : EType n m k) (f : FinFun n n') (g : FinFun n' n'') :
  (E.rename f).rename g = E.rename (g ∘ f) :=
  match E with
  | EType.ex T => by
    have ih := CType.rename_rename T f g
    simp [EType.rename, ih]
  | EType.type T => by
    have ih := CType.rename_rename T f g
    simp [EType.rename, ih]

theorem CType.rename_rename (T : CType n m k) (f : FinFun n n') (g : FinFun n' n'') :
  (T.rename f).rename g = T.rename (g ∘ f) :=
  match T with
  | CType.capt C S => by
    have ih1 := CaptureSet.rename_rename (C := C) (f := f) (g := g)
    have ih2 := SType.rename_rename S f g
    simp [CType.rename, ih1, ih2]

theorem SType.rename_rename (S : SType n m k) (f : FinFun n n') (g : FinFun n' n'') :
  (S.rename f).rename g = S.rename (g ∘ f) :=
  match S with
  | SType.top => by simp [SType.rename]
  | SType.tvar X => by simp [SType.rename]
  | SType.forall E1 E2 => by
    have ih1 := CType.rename_rename E1 f g
    have ih2 := EType.rename_rename E2 f.ext g.ext
    simp [SType.rename, ih1, ih2, FinFun.ext_comp_ext]
  | SType.tforall S E => by
    have ih1 := SType.rename_rename S f g
    have ih2 := EType.rename_rename E f g
    simp [SType.rename, ih1, ih2]
  | SType.cforall E => by
    have ih := EType.rename_rename E f g
    simp [SType.rename, ih]
  | SType.box T => by
    have ih := CType.rename_rename T f g
    simp [SType.rename, ih]

end

theorem EType.weaken_rename {E : EType n m k} :
  (E.rename f).weaken = E.weaken.rename f.ext := by
  simp [weaken, rename_rename, FinFun.comp_weaken]

theorem CType.weaken_rename {C : CType n m k} :
  (C.rename f).weaken = C.weaken.rename f.ext := by
  simp [weaken, rename_rename, FinFun.comp_weaken]

mutual


theorem EType.trename_rename_comm (E : EType n m k) (f : FinFun n n') (g : FinFun m m') :
  (E.trename g).rename f = (E.rename f).trename g :=
  match E with
  | EType.ex T => by
    have ih := CType.trename_rename_comm T f g
    simp [EType.trename, EType.rename, ih]
  | EType.type T => by
    have ih := CType.trename_rename_comm T f g
    simp [EType.trename, EType.rename, ih]

theorem CType.trename_rename_comm (T : CType n m k) (f : FinFun n n') (g : FinFun m m') :
  (T.trename g).rename f = (T.rename f).trename g :=
  match T with
  | CType.capt C S => by
    have ih2 := SType.trename_rename_comm S f g
    simp [CType.trename, CType.rename, ih2]

theorem SType.trename_rename_comm (S : SType n m k) (f : FinFun n n') (g : FinFun m m') :
  (S.trename g).rename f = (S.rename f).trename g :=
  match S with
  | SType.top => by simp [SType.trename, SType.rename]
  | SType.tvar X => by simp [SType.trename, SType.rename]
  | SType.forall E1 E2 => by
    have ih1 := CType.trename_rename_comm E1 f g
    have ih2 := EType.trename_rename_comm E2 f.ext g
    simp [SType.trename, SType.rename, ih1, ih2]
  | SType.tforall S E => by
    have ih1 := SType.trename_rename_comm S f g
    have ih2 := EType.trename_rename_comm E f g.ext
    simp [SType.trename, SType.rename, ih1, ih2]
  | SType.cforall E => by
    have ih := EType.trename_rename_comm E f g
    simp [SType.trename, SType.rename, ih]
  | SType.box T => by
    have ih := CType.trename_rename_comm T f g
    simp [SType.trename, SType.rename, ih]

end

mutual

theorem EType.crename_crename (E : EType n m k) (f : FinFun k k') (g : FinFun k' k'') :
  (E.crename f).crename g = E.crename (g ∘ f) :=
  match E with
  | EType.ex T => by
    have ih := CType.crename_crename T f.ext g.ext
    simp [EType.crename, CType.crename, ih, FinFun.ext_comp_ext]
  | EType.type T => by
    have ih := CType.crename_crename T f g
    simp [EType.crename, CType.crename, ih]

theorem CType.crename_crename (T : CType n m k) (f : FinFun k k') (g : FinFun k' k'') :
  (T.crename f).crename g = T.crename (g ∘ f) :=
  match T with
  | CType.capt C S => by
    have ih2 := SType.crename_crename S f g
    simp [CType.crename, CaptureSet.crename_crename, ih2]

theorem SType.crename_crename (S : SType n m k) (f : FinFun k k') (g : FinFun k' k'') :
  (S.crename f).crename g = S.crename (g ∘ f) :=
  match S with
  | SType.top => by simp [SType.crename]
  | SType.tvar X => by simp [SType.crename]
  | SType.forall E1 E2 => by
    have ih1 := CType.crename_crename E1 f g
    have ih2 := EType.crename_crename E2 f g
    simp [SType.crename, ih1, ih2]
  | SType.tforall S E => by
    have ih1 := SType.crename_crename S f g
    have ih2 := EType.crename_crename E f g
    simp [SType.crename, ih1, ih2]
  | SType.cforall E => by
    have ih := EType.crename_crename E f.ext g.ext
    simp [SType.crename, ih, FinFun.ext_comp_ext]
  | SType.box T => by
    have ih := CType.crename_crename T f g
    simp [SType.crename, ih]

end

mutual

theorem EType.crename_trename_comm (E : EType n m k) (f : FinFun k k') (g : FinFun m m') :
  (E.crename f).trename g = (E.trename g).crename f :=
  match E with
  | EType.ex T => by
    have ih := CType.crename_trename_comm T f.ext g
    simp [EType.crename, EType.trename, ih]
  | EType.type T => by
    have ih := CType.crename_trename_comm T f g
    simp [EType.crename, EType.trename, ih]

theorem CType.crename_trename_comm (T : CType n m k) (f : FinFun k k') (g : FinFun m m') :
  (T.crename f).trename g = (T.trename g).crename f :=
  match T with
  | CType.capt C S => by
    have ih2 := SType.crename_trename_comm S f g
    simp [CType.crename, CType.trename, ih2]

theorem SType.crename_trename_comm (S : SType n m k) (f : FinFun k k') (g : FinFun m m') :
  (S.crename f).trename g = (S.trename g).crename f :=
  match S with
  | SType.top => by simp [SType.crename, SType.trename]
  | SType.tvar X => by simp [SType.crename, SType.trename]
  | SType.forall E1 E2 => by
    have ih1 := CType.crename_trename_comm E1 f g
    have ih2 := EType.crename_trename_comm E2 f g
    simp [SType.crename, SType.trename, ih1, ih2]
  | SType.tforall S E => by
    have ih1 := SType.crename_trename_comm S f g
    have ih2 := EType.crename_trename_comm E f g.ext
    simp [SType.crename, SType.trename, ih1, ih2]
  | SType.cforall E => by
    have ih := EType.crename_trename_comm E f.ext g
    simp [SType.crename, SType.trename, ih]
  | SType.box T => by
    have ih := CType.crename_trename_comm T f g
    simp [SType.crename, SType.trename, ih]

end

def EType.tweaken_rename {E : EType n m k} :
  E.tweaken.rename f = (E.rename f).tweaken := by
  simp [tweaken, trename, trename_rename_comm]

theorem CType.tweaken_rename {C : CType n m k} :
  C.tweaken.rename f = (C.rename f).tweaken := by
  simp [tweaken, trename, trename_rename_comm]

def EType.rename_open :
  (EType.open E x).rename f = (E.rename f.ext).open (f x) := by
  simp [EType.open]
  simp [EType.rename_rename]
  simp [FinFun.open_comp]

theorem EType.rename_topen :
  (EType.topen E X).rename f = (E.rename f).topen X := by
  simp [EType.topen, EType.rename]
  simp [EType.trename_rename_comm]

theorem EType.rename_copen :
  (EType.copen E c).rename f = (E.rename f).copen c := by
  simp [EType.copen, EType.rename]
  simp [EType.crename_rename_comm]

theorem EType.cweaken_crename {E : EType n m k} :
  (E.crename f).cweaken = E.cweaken.crename f.ext := by
  simp [cweaken, crename_crename, FinFun.comp_weaken]

theorem CType.cweaken_crename {C : CType n m k} :
  (C.crename f).cweaken = C.cweaken.crename f.ext := by
  simp [cweaken, crename_crename, FinFun.comp_weaken]

theorem EType.weaken_crename {E : EType n m k} :
  (E.crename f).weaken = E.weaken.crename f := by
  simp [weaken, crename_rename_comm]

theorem CType.weaken_crename {C : CType n m k} :
  (C.crename f).weaken = C.weaken.crename f := by
  simp [weaken, crename_rename_comm]

theorem EType.tweaken_crename {E : EType n m k} :
  (E.crename f).tweaken = E.tweaken.crename f := by
  simp [tweaken, crename_trename_comm]

theorem CType.tweaken_crename {C : CType n m k} :
  (C.crename f).tweaken = C.tweaken.crename f := by
  simp [tweaken, crename_trename_comm]

theorem EType.crename_copen {E : EType n m (k+1)} :
  (E.copen c).crename f = (E.crename f.ext).copen (f c) := by
  simp [copen, crename_crename, FinFun.open_comp]

theorem SType.crename_copen {S : SType n m (k+1)} :
  (S.copen c).crename f = (S.crename f.ext).copen (f c) := by
  simp [copen, crename_crename, FinFun.open_comp]

theorem CType.crename_copen {C : CType n m (k+1)} :
  (C.copen c).crename f = (C.crename f.ext).copen (f c) := by
  simp [copen, crename_crename, FinFun.open_comp]

theorem EType.crename_open {E : EType (n+1) m k} :
  (E.open x).crename f = (E.crename f).open x := by
  simp [EType.open, crename_rename_comm, FinFun.open_comp]

theorem EType.crename_topen {E : EType n (m+1) k} :
  (E.topen X).crename f = (E.crename f).topen X := by
  simp [EType.topen, crename_trename_comm]

theorem EType.weaken_trename {E : EType n m k} :
  (E.trename f).weaken = E.weaken.trename f := by
  simp [weaken, trename_rename_comm]

theorem CType.weaken_trename {C : CType n m k} :
  (C.trename f).weaken = C.weaken.trename f := by
  simp [weaken, trename_rename_comm]

mutual

theorem EType.trename_trename (E : EType n m k) (f : FinFun m m') (g : FinFun m' m'') :
  (E.trename f).trename g = E.trename (g ∘ f) :=
  match E with
  | EType.ex T => by
    have ih := CType.trename_trename T f g
    simp [EType.trename, ih]
  | EType.type T => by
    have ih := CType.trename_trename T f g
    simp [EType.trename, ih]

theorem CType.trename_trename (T : CType n m k) (f : FinFun m m') (g : FinFun m' m'') :
  (T.trename f).trename g = T.trename (g ∘ f) :=
  match T with
  | CType.capt C S => by
    have ih2 := SType.trename_trename S f g
    simp [CType.trename, ih2]

theorem SType.trename_trename (S : SType n m k) (f : FinFun m m') (g : FinFun m' m'') :
  (S.trename f).trename g = S.trename (g ∘ f) :=
  match S with
  | SType.top => by simp [SType.trename]
  | SType.tvar X => by simp [SType.trename]
  | SType.forall E1 E2 => by
    have ih1 := CType.trename_trename E1 f g
    have ih2 := EType.trename_trename E2 f g
    simp [SType.trename, ih1, ih2]
  | SType.tforall S E => by
    have ih1 := SType.trename_trename S f g
    have ih2 := EType.trename_trename E f.ext g.ext
    simp [SType.trename, ih1, ih2, FinFun.ext_comp_ext]
  | SType.cforall E => by
    have ih := EType.trename_trename E f g
    simp [SType.trename, ih]
  | SType.box T => by
    have ih := CType.trename_trename T f g
    simp [SType.trename, ih]

end

theorem SType.cweaken_trename {S : SType n m k} :
  (S.trename f).cweaken = S.cweaken.trename f := by
  simp [cweaken, crename_trename_comm]

theorem SType.cweaken_crename {S : SType n m k} :
  (S.crename f).cweaken = S.cweaken.crename f.ext := by
  simp [cweaken, crename_crename, FinFun.comp_weaken]

theorem SType.weaken_trename {S : SType n m k} :
  (S.trename f).weaken = S.weaken.trename f := by
  simp [weaken, SType.trename_rename_comm]

theorem SType.tweaken_trename {S : SType n m k} :
  (S.trename f).tweaken = S.tweaken.trename f.ext := by
  simp [tweaken, trename_trename, FinFun.comp_weaken]

theorem EType.tweaken_trename {E : EType n m k} :
  (E.trename f).tweaken = E.tweaken.trename f.ext := by
  simp [tweaken, trename_trename, FinFun.comp_weaken]

theorem CType.tweaken_trename {C : CType n m k} :
  (C.trename f).tweaken = C.tweaken.trename f.ext := by
  simp [tweaken, trename_trename, FinFun.comp_weaken]

theorem EType.cweaken_trename {E : EType n m k} :
  (E.trename f).cweaken = E.cweaken.trename f := by
  simp [cweaken, crename_trename_comm]

theorem CType.cweaken_trename {E : CType n m k} :
  (E.trename f).cweaken = E.cweaken.trename f := by
  simp [cweaken, crename_trename_comm]

theorem EType.trename_copen {E : EType n m (k+1)} :
  (E.copen c).trename f = (E.trename f).copen c := by
  simp [copen, crename_trename_comm]

theorem SType.trename_copen {S : SType n m (k+1)} :
  (S.copen c).trename f = (S.trename f).copen c := by
  simp [copen, crename_trename_comm]

theorem CType.trename_copen {C : CType n m (k+1)} :
  (C.copen c).trename f = (C.trename f).copen c := by
  simp [copen, crename_trename_comm]

theorem EType.trename_open {E : EType (n+1) m k} :
  (E.open x).trename f = (E.trename f).open x := by
  simp [EType.open, trename_rename_comm]

theorem EType.trename_topen {E : EType n (m+1) k} :
  (E.topen X).trename f = (E.trename f.ext).topen (f X) := by
  simp [EType.topen, EType.trename_trename, FinFun.open_comp]

theorem EType.cweaken_eq_inv {E : EType n m k}
  (heq : EType.type (CType.capt C S) = E.cweaken) :
  ∃ C0 S0, E = EType.type (CType.capt C0 S0) ∧ C0.cweaken = C ∧ S0.cweaken = S := by
  cases E
  case ex => simp [cweaken, crename] at heq
  case type T =>
    cases T; rename_i C0 S0
    simp [EType.cweaken, EType.crename, CType.crename] at heq
    exists C0; exists S0
    simp [CaptureSet.cweaken, SType.cweaken]; aesop

theorem EType.ex_cweaken_eq_inv {E : EType n m k}
  (heq : EType.ex (CType.capt C S) = E.cweaken) :
  ∃ C0 S0, E = EType.ex (CType.capt C0 S0) ∧ C0.cweaken1 = C ∧ S0.cweaken1 = S := by
  cases E
  case type => simp [cweaken, crename] at heq
  case ex T =>
    cases T; rename_i C0 S0
    simp [EType.cweaken, EType.crename, CType.crename] at heq
    exists C0, S0
    simp [CaptureSet.cweaken1, SType.cweaken1]; aesop

mutual

theorem EType.rename_id {E : EType n m k} :
  E.rename FinFun.id = E :=
  match E with
  | EType.ex T => by
    have ih := CType.rename_id (T := T)
    simp [EType.rename, ih]
  | EType.type T => by
    have ih := CType.rename_id (T := T)
    simp [EType.rename, ih]

theorem CType.rename_id {T : CType n m k} :
  T.rename FinFun.id = T :=
  match T with
  | CType.capt C S => by
    have ih1 := CaptureSet.rename_id (C := C)
    have ih2 := SType.rename_id (S := S)
    simp [CType.rename, ih1, ih2]

theorem SType.rename_id {S : SType n m k} :
  S.rename FinFun.id = S :=
  match S with
  | SType.top => by simp [SType.rename]
  | SType.tvar X => by simp [SType.rename]
  | SType.forall E1 E2 => by
    have ih1 := CType.rename_id (T := E1)
    have ih2 := EType.rename_id (E := E2)
    simp [SType.rename, FinFun.id_ext, ih1, ih2]
  | SType.tforall S E => by
    have ih1 := SType.rename_id (S := S)
    have ih2 := EType.rename_id (E := E)
    simp [SType.rename, ih1, ih2]
  | SType.cforall E => by
    have ih := EType.rename_id (E := E)
    simp [SType.rename, ih]
  | SType.box T => by
    have ih := CType.rename_id (T := T)
    simp [SType.rename, ih]

end

mutual

theorem EType.trename_id {E : EType n m k} :
  E.trename FinFun.id = E :=
  match E with
  | EType.ex T => by
    have ih := CType.trename_id (T := T)
    simp [EType.trename, ih]
  | EType.type T => by
    have ih := CType.trename_id (T := T)
    simp [EType.trename, ih]

theorem CType.trename_id {T : CType n m k} :
  T.trename FinFun.id = T :=
  match T with
  | CType.capt C S => by
    have ih2 := SType.trename_id (S := S)
    simp [CType.trename, ih2]

theorem SType.trename_id {S : SType n m k} :
  S.trename FinFun.id = S :=
  match S with
  | SType.top => by simp [SType.trename]
  | SType.tvar X => by simp [SType.trename, FinFun.id]
  | SType.forall E1 E2 => by
    have ih1 := CType.trename_id (T := E1)
    have ih2 := EType.trename_id (E := E2)
    simp [SType.trename, FinFun.id_ext, ih1, ih2]
  | SType.tforall S E => by
    have ih1 := SType.trename_id (S := S)
    have ih2 := EType.trename_id (E := E)
    simp [SType.trename, FinFun.id_ext, ih1, ih2]
  | SType.cforall E => by
    have ih := EType.trename_id (E := E)
    simp [SType.trename, ih]
  | SType.box T => by
    have ih := CType.trename_id (T := T)
    simp [SType.trename, ih]

end

mutual

theorem EType.crename_id {E : EType n m k} :
  E.crename FinFun.id = E :=
  match E with
  | EType.ex T => by
    have ih := CType.crename_id (T := T)
    simp [EType.crename, FinFun.id_ext, ih]
  | EType.type T => by
    have ih := CType.crename_id (T := T)
    simp [EType.crename, ih]

theorem CType.crename_id {T : CType n m k} :
  T.crename FinFun.id = T :=
  match T with
  | CType.capt C S => by
    have ih1 := CaptureSet.crename_id (C := C)
    have ih2 := SType.crename_id (S := S)
    simp [CType.crename, ih1, ih2]

theorem SType.crename_id {S : SType n m k} :
  S.crename FinFun.id = S :=
  match S with
  | SType.top => by simp [SType.crename]
  | SType.tvar X => by simp [SType.crename]
  | SType.forall E1 E2 => by
    have ih1 := CType.crename_id (T := E1)
    have ih2 := EType.crename_id (E := E2)
    simp [SType.crename, ih1, ih2]
  | SType.tforall S E => by
    have ih1 := SType.crename_id (S := S)
    have ih2 := EType.crename_id (E := E)
    simp [SType.crename, ih1, ih2]
  | SType.cforall E => by
    have ih := EType.crename_id (E := E)
    simp [SType.crename, FinFun.id_ext, ih]
  | SType.box T => by
    have ih := CType.crename_id (T := T)
    simp [SType.crename, ih]

end

theorem SType.tvar_tweaken_succ :
  (SType.tvar X : SType n m k).tweaken = SType.tvar X.succ := by
  simp [SType.tweaken, SType.trename, FinFun.weaken]

end Capless
