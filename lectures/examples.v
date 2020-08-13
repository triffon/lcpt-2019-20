Require Import ZArith.

Section Example.
  Check 0.
  Check nat.
  Check Set.
  Check Type.
  
  Variable n : nat.
  Hypothesis Pos_n : n > 0.
  Check n.
  Check Pos_n.
  Check n > 0.
  Check Prop.
  Check gt.
  Check bool.
  Definition ispos (n : nat) : bool := 
     match n with
       | O => false
       | S m => true
     end.
  Check ispos.
  Definition ispos2 (n : nat) : Prop := n > 0.
  Check ispos2.
End Example.

Section Example2.
  Check S.
  Check O.
  Definition one := S O.
  Check one.
  Definition four := S (S (S one)).
  Check four.
  Check plus.
  Definition double (m : nat) := plus m m.
  Check double.
  Print double.
  Print four.
  Compute four.
  Print gt.
  Check _<_.
  Compute double four.
  Check forall m:nat, m > 0.
End Example2.

Section MinLog.
  Variable A B C : Prop.
  Check A -> A.
  Goal A -> A.
  intro H. (* (assume "H") *)
  apply H. (* (use "H") *)
  Save Identity.
  Print Identity.
  
  Lemma K : A -> B -> A.
    intros H1 H2.
    apply H1.
  Qed.
  
  Lemma S : (A -> B -> C) -> (A -> B) -> A -> C.
    auto.
  Qed.
  
  Print S.
  
  Lemma commutativity : A /\ B -> B /\ A.
    intro.
    elim H.
    (*
    split.
    apply H1.
    apply H0.*)
    (* split; [ apply H1 | apply H0 ]. *)
    split; [ assumption | assumption ].
  Qed.
  
  Print commutativity.
  
  Definition comm2 : A /\ B -> B /\ A := fun H : A /\ B => and_ind (fun (H0 : A) (H1 : B) => conj H1 H0) H.
  
End MinLog.

Section ClassLog.
  Variable A : Prop.
  (*
  Hypothesis Stab : ~~A -> A.
  *)
  Hypothesis Stab : forall A : Prop, ~~A -> A.
  Check Stab.
  Check forall A : Prop, ~~A -> A.
  
  Theorem LEM : A \/ ~A.
    apply (Stab (A \/ ~A)).
    intro H.
    apply H.
    apply or_introl.
    apply (Stab A).
    intro H1.
    apply H.
    apply or_intror.
    assumption.
  Qed.
  
  Print LEM.
End ClassLog.

Section PredLog.
  Variable p : nat -> Prop.
  Lemma forallexists : (forall x : nat, p x) -> exists x : nat, p x.
    intro H.
    apply (ex_intro _ O).
    apply (H 0).
  Qed.

  
  Variable α : Set.
  Variable xα : α.
  Variable pα : α  -> Prop.
  Lemma forallexistsα : (forall x : α, pα  x) -> exists x : α , pα  x.
    intro H.
    apply (ex_intro _ xα).
    apply (H xα).
  Qed.

  Variable Rα : α -> α -> Prop.
  Hypothesis Rα_sym : forall x y : α, Rα x y -> Rα y x.
  Hypothesis Rα_trans : forall x y z : α, (Rα x y -> Rα y z -> Rα x z).
  Lemma Rα_refl : forall x : α, (exists y : α, Rα x y) -> Rα x x.
    intros x H.
    elim H; intros y xRαy.
    apply Rα_trans with y.
    assumption.
    apply Rα_sym; assumption.
  Qed.
  Print Rα_refl.
End PredLog.
