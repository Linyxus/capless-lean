inductive MemKind: Type -- classifies names/members
| field -- names of term members
| type  -- names of type members

inductive Ty: Nat -> Type -- for simplicity, just one case
| bot: Ty n

inductive ComponentSig: Nat -> MemKind -> Type -- classifies the dependent second component of a pair _type_
| field : Ty n -> ComponentSig n field         -- field member of type T
| type  : Ty n -> Ty n -> ComponentSig n type  -- type member with interval S .. T

def ComponentSig.interval' (sig : ComponentSig n K) : Ty n × Ty n := by
  cases sig
  case field => sorry
  case type => sorry
