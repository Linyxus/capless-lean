namespace Cappy

structure TMap (n m k : Nat) where
  reach : Fin n -> Fin k
  treach : Fin m -> Fin k

end Cappy
