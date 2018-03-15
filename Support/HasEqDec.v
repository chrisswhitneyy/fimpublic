Module Type HasEqDec.
  Parameter A : Set.
  Parameter eq_dec : forall x y : A, { x=y } + { x<>y }.
End HasEqDec.
