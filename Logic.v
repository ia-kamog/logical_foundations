Set Warnings "-notation-overriden, -parsing".
Require Export Tactics.
Check 3=3.
Check forall n m: nat, n + m = m + n.
Check 2=2.
Check forall n:nat, n = 2.
Check 3 = 4.
Theorem plus_2_2_is_4:
  2+2=4.
Proof. reflexivity. Qed.
Definition plus_fact: Prop := 2 + 2 = 4.
Check plus_fact.
Theorem plus_fact_is_true: plus_fact.
Proof. reflexivity. Qed.
Definition is_three (n:nat): Prop := n = 3.
Check is_three.
Definition injective {A B} (f: A -> B) :=
  forall x y: A, f x = f y -> x = y.

Lemma succ_inj: injective S.
Proof. intros n m H. inversion H. reflexivity. Qed.
Check @eq.

Example and_example: 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.
Lemma and_intro: forall A B: Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_example': 3 + 4 = 7 /\ 2 * 2 = 4.
Proof. apply and_intro; reflexivity. Qed.

(** *Exercise and_exercise *)
Example and_exercise:
  forall n m: nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  destruct n as [|n]; destruct m as [|m]; intros H; try inversion H.
  split; reflexivity.
Qed.

Lemma and_example2: forall n m: nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H. destruct H as [Hn Hm]. rewrite Hn, Hm. reflexivity. Qed.

Lemma and_example2': forall n m: nat, n = 0 /\ m = 0 -> n + m = 0.
Proof. intros n m [Hn Hm]. rewrite Hn, Hm. reflexivity. Qed.
Lemma and_example2'': forall n m: nat, n = 0 -> m = 0 -> n + m = 0.
Proof. intros n m Hn Hm. rewrite Hn, Hm. reflexivity. Qed.
Lemma and_example3:
  forall n m: nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.
Lemma proj1: forall P Q: Prop, P /\ Q -> P.
Proof. intros P Q [HP HQ]. exact HP. Qed.
(** *Exercise proj2 *)
Lemma proj2: forall P Q: Prop, P /\ Q -> Q.
Proof. intros P Q [_ HQ]. exact HQ. Qed.
Theorem and_commit: forall P Q: Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ]. split.
  - exact HQ.
  - exact HP.
Qed.
(** *Exercise and_assoc *)
Theorem and_assoc: forall P Q R: Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]]. split.
  - split.
    + exact HP.
    + exact HQ.
  - exact HR.
Qed.
Check and.

Lemma or_example:
  forall n m: nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. symmetry. apply mult_n_O.
Qed.
Lemma or_intro: forall A B: Prop, A -> A \/ B.
Proof. intros A B HA. left. exact HA. Qed.

Lemma zero_or_succ: forall n: nat, n = 0 \/ n = S (pred n).
Proof.
  intros [| n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** *Exercise mult_eq_0 *)
Lemma mult_eq_0: forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. destruct n.
  - left. reflexivity.
  - simpl in H. apply and_exercise in H. destruct H as [H _].
    right. exact H.
Qed.

(** *Exericse or_commut *)
Theorem or_commut: forall P Q: Prop, P \/ Q -> Q \/ P.
Proof. intros P Q [p|q].
       - right. exact p.
       - left. exact q.
Qed.
Module MyNot.
  Definition not (P:Prop) := P -> False.
  Notation "~ x" := (not x): type_scope.
  Check not.
End MyNot.
Theorem ex_falso_quodlibet: forall P: Prop, False -> P.
Proof. intros P contra. destruct contra. Qed.
Fact not_implies_our_not: forall P : Prop,
    ~ P -> (forall Q: Prop, P -> Q).
Proof.
  intros P H Q p. apply H in p. destruct p. Qed.
Theorem zero_not_one: ~(0 = 1).
Proof. intros contra. inversion contra. Qed.
Check (0 <> 1).
Theorem zero_not_one': 0 <> 1.
Proof.
  intros H. inversion H. Qed.

Theorem not_False: ~ False.
Proof. unfold not. intros H. destruct H. Qed.
Theorem contradiction_implies_anything: forall P Q: Prop,
    P /\ ~P -> Q.
Proof.
  intros P Q [p np]. apply np in p. destruct p. Qed.

Theorem double_neg: forall P: Prop, P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H. Qed.

(** *Exercise double_neg_inf 
P implies ~~P for any P.
Assume P. We need to prove ~~P, or that ~P doesn't hold.
Indeed, if ~P holds, then P taken with ~P is a contradiction. *)
(** *Exercise contrapositive *)
Theorem contrapositive: forall P Q: Prop,
    (P -> Q) -> (~Q -> ~P).
Proof. intros P Q H NQ p. apply NQ. apply H. exact p. Qed.
(** *Exercise not_both_true_and_false *)
Theorem not_both_true_and_false: forall P: Prop, ~ (P /\ ~P).
Proof. intros P [p np]. apply np. exact p. Qed.
(** *Exercise informal_not_PNP *)
Definition informal_not_PNP_TODO := 1.
(* for any proposition P, ~(P /\ ~ P).
   That is, P /\ ~P implies anything.
   Indeed P /\ ~P contrains both P and ~P, which give False term. *)
Theorem not_true_is_false: forall b: bool, b <> true -> b = false.
Proof. intros [|] H.
       - exfalso. apply H. reflexivity.
       - reflexivity. Qed.
Lemma True_is_true: True.
Proof. apply I. Qed.

Module MyIff.
  Definition iff (P Q: Prop) := (P -> Q) /\ (Q -> P).
  Notation "P <-> Q" := (iff P Q) (at level 95, no associativity): type_scope.
End MyIff.
Theorem iff_sym: forall P Q: Prop, (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA]. split.
  - apply HBA.
  - apply HAB.
Qed.
Lemma not_true_iff_false: forall b, b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  - intros H. rewrite H. intros H'. inversion H'.
Qed.

(** *Exercise or_distributes_over_and *)
Theorem or_distributes_over_and: forall P Q R: Prop, P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split; intros H.
  - destruct H as [p|H2]; split; try destruct H2 as [q r].
    + left. exact p.
    + left. exact p.
    + right. exact q.
    + right. exact r.
  - destruct H as [H1 H2]. destruct H1 as [p|q].
    + left. exact p.
    + destruct H2 as [p|r].
      * left. exact p.
      * right. split. exact q. exact r.
Qed.

Require Import Coq.Setoids.Setoid.
Lemma mult_0: forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.
Lemma or_assoc: forall P Q R: Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H|[H|H]]; [left;left|left;right|right]; exact H.
  - intros [[H|H]|H]; [left|right;left|right;right]; exact H.
Qed.
Lemma mult_0_3:
  forall n m p, n*m*p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p. rewrite mult_0, mult_0, or_assoc.
  reflexivity. Qed.

Lemma four_is_even: exists n: nat, 4 = n + n.
Proof. exists 2. reflexivity. Qed.

Theorem exists_example_2: forall n, (exists m, n = 4 + m) -> exists o, n = 2 + o.
Proof.
  intros n [m Hm]. exists (2+m). apply Hm. Qed.
(** *Exercise dist_not_exist *)
Theorem dist_not_exist: forall (X: Type)(P: X -> Prop),
    (forall x, P x) -> ~(exists x, ~ P x).
Proof.
  intros X P H E. destruct E as [e p]. apply p. apply H.
Qed.
(** *Exercise dist_exists_or *)
Theorem dist_exists_or: forall (X: Type)(P Q: X -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros [x [p|q]].
    + left. exists x. exact p.
    + right. exists x. exact q.
  - intros [[x p]|[x q]]; exists x.
    + left. exact p.
    + right. exact q.
Qed.
