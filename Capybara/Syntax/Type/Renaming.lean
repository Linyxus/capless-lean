import Capybara.Syntax.Type.Core
namespace Capybara

def SepDegree.rename
  (D : SepDegree n k)
  (ρ : Renaming n m k n' m' k') :
  SepDegree n' k' :=
  match D with
  | ⟨s, C⟩ => ⟨s, C.rename ρ⟩

mutual

def EType.rename
  (E : EType n m k)
  (ρ : Renaming n m k n' m' k') :
  EType n' m' k' :=
  match E with
  | EType.type T => EType.type (T.rename ρ)
  | EType.ex T => EType.ex (T.rename ρ.cext)

def CType.rename
  (T : CType n m k)
  (ρ : Renaming n m k n' m' k') :
  CType n' m' k' :=
  match T with
  | CType.capt C m S => CType.capt (C.rename ρ) m (S.rename ρ)

def SType.rename (S : SType n m k) (ρ : Renaming n m k n' m' k') : SType n' m' k' :=
  match S with
  | SType.top => SType.top
  | SType.tvar x => SType.tvar (ρ.tvar x)
  | SType.arrow T E => (x:T.rename ρ)->(E.rename ρ.ext)
  | SType.carrow D E => [c:D.rename ρ]->(E.rename ρ.cext)
  | SType.farrow T E => [c:Fresh](x:T.rename ρ.cext)->(E.rename ρ.cext.ext)
  | SType.tarrow S T => [X<:S.rename ρ]->(T.rename ρ.text)

end

end Capybara
