Require Import SyDPaCC.FIM.Support.HasEqDec.
        
Module Type AOrder (Import A: HasEqDec).
  
  Parameter leb : A -> A -> bool.
  Parameter le : A -> A -> Prop.

  Axiom le_refl : forall x, le x x.
  Axiom le_trans : forall x y z, le x y -> le y z -> le x z.
  Axiom le_antisym : forall x y, le x y -> le y x -> x = y.
  Parameter le_dec : forall x y, {le x y} + {~ (le x y)}.
  
  Axiom leb_le : forall n m : A, (leb n m) = true <-> (le n m).
  Axiom leb_nle : forall n m : A, (leb n m) = false <-> not (le n m).
    
End AOrder.
