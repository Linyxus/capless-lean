import Capybara.Syntax.Type.Core
namespace Capybara

mutual

def EType.rename (E : EType n m k) (f : FinFun n n') : EType n' m k :=
  match E with
  | EType.type T => EType.type (T.rename f)
  | EType.ex T => EType.ex (T.rename f)

def CType.rename (T : CType n m k) (f : FinFun n n') : CType n' m k :=
  match T with
  | CType.capt C m S => CType.capt (C.rename f) m (S.rename f)

def SType.rename (S : SType n m k) (f : FinFun n n') : SType n' m k :=
  match S with
  | SType.top => SType.top
  | SType.tvar x => SType.tvar x
  | SType.arrow T E => (x:T.rename f)->(E.rename f.ext)
  | SType.carrow k E => [c:k]->(E.rename f)
  | SType.tarrow S T => [X<:S.rename f]->(T.rename f)

end

end Capybara
