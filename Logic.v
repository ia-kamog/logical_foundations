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

Fixpoint In {A: Type}(x: A)(l: list A): Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1: In 4 [1;2;3;4;5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2: forall n, In n [2;4] -> exists n', n = 2 * n'.
Proof.
  simpl. intros n [H|[H|[]]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map: forall (A B: Type)(f: A -> B) (l: list A)(x: A),
    In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - simpl. intros [].
  - simpl. intros [H|H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(** *Exercise in_map_iff *)
Lemma and_distributes_over_or: forall P Q R: Prop, P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
  intros P Q R. split.
  - intros [p [q|r]].
    + left. split; [exact p|exact q].
    + right. split; [exact p|exact r].
  - intros [[p q]|[p r]].
    + split; [exact p|left;exact q].
    + split; [exact p|right;exact r].
Qed.
Lemma In_map_iff:
  forall (A B: Type) (f: A -> B) (l: list A) (y: B),
    In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f. induction l as [|h t I]; intros y; simpl; split.
  - intros [].
  - intros [_ [_ []]].
  - intros [H|H].
    + exists h. split; [exact H|left;reflexivity].
    + apply I in H. destruct H as [m H]. exists m.
      rewrite -> and_distributes_over_or. right. exact H.
  - intros [m [H [H'|H']]].
    + rewrite H'. left. exact H.
    + right. apply I. exists m. split; [exact H|exact H'].
Qed.

(** *Exersie In_app_iff *)
Lemma In_app_iff: forall A l l' (a: A),
    In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a. generalize dependent l'. induction l as [|h t IH].
  - intros l'. simpl. split.
    + intros H; right; exact H.
    + intros [H|H]; [inversion H|exact H].
  - intros l'. simpl. split.
    + intros [H|H].
      * left. left. exact H.
      * rewrite <- or_assoc. right. apply IH. exact H.
    + intros [[H|H]|H].
      * left. exact H.
      * right. apply IH. left. exact H.
      * right. apply IH. right. exact H.
Qed.

(** *Exercise All *)
Fixpoint All {T: Type} (P: T -> Prop) (l: list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.
Lemma All_in: forall T (P: T -> Prop)(l: list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l. induction l as [|h t IH].
  - simpl. split.
    + intros _. apply I.
    + intros _ x [].
  - simpl. split.
    + intros H. split.
      * apply H. left. reflexivity.
      * apply IH. intros x H1. apply H. right. exact H1.
    + intros [H1 H2] x [H3|H3].
      * rewrite <- H3. exact H1.
      * apply IH. exact H2. exact H3.
Qed.

(** *Exercise combine_odd_even *)
Definition combine_odd_even (Podd Peven: nat -> Prop): nat -> Prop :=
  fun n: nat => if oddb n then Podd n else Peven n.

Theorem combine_odd_even_intro:
  forall (Podd Peven: nat -> Prop)(n:nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n Ho He. unfold combine_odd_even.
  destruct (oddb n).
  - apply Ho. reflexivity.
  - apply He. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd: forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n -> oddb n = true -> Podd n.
Proof.
  intros Podd Peven n H H'. unfold combine_odd_even in H.
  destruct (oddb n).
  - exact H.
  - inversion H'.
Qed.

Theorem combine_odd_even_elim_even: forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n -> oddb n = false -> Peven n.
Proof.
  unfold combine_odd_even. intros Podd Peven n H H'. destruct (oddb n).
  - inversion H'.
  - exact H.
Qed.

Check plus_comm.

Lemma plus_comm3:
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z. rewrite plus_comm. rewrite plus_comm. Abort.

Lemma plus_comm3_take2:
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma plu_comm3_take3:
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Example lemma_application_ex:
  forall {n: nat} {ns: list nat},
    In n (map (fun m => m * 0) ns) -> n = 0.
Proof.
  intros n ns H.
  destruct (proj1  _ _ (In_map_iff _ _ _ _ _) H) as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

Example function_equality_ex1: plus 3 = plus (pred 4).
Proof. reflexivity. Qed.

Example function_equality_ex2:
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
Abort.

Axiom functional_extensionality: forall {X Y: Type} {f g: X -> Y},
    (forall x, f x = g x) -> f = g.

Example function_equality_ex2:
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros x. apply plus_comm.
Qed.

Print Assumptions function_equality_ex2.
(** *Exercise tr_rev_correct *)
Fixpoint rev_append {X} (l1 l2: list X): list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l: list X): list X :=
  rev_append l [].

Lemma tr_rev_correct: forall X, @tr_rev X = @rev X.
Proof.
  assert (L: forall X (l1 l2: list X), rev_append l1 l2 = rev l1 ++ l2).
  {
    intros X. induction l1 as [|h t IH].
    - simpl. intros. reflexivity.
    - intros l2. simpl. rewrite <- app_assoc. simpl. apply IH.
  }
  intros X. apply functional_extensionality. unfold tr_rev.
  destruct x as [|h t].
  - reflexivity.
  - simpl. apply L.
Qed.

Theorem evenb_double: forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** *Exercise evenb_double_conv *)
Theorem evenb_double_conv : forall n,
    exists k, n = if evenb n then double k else S (double k).
Proof.
  induction n as [|n' IHn'].
  - exists 0. reflexivity.
  - destruct IHn' as [k H].
    destruct (evenb (S n')) eqn:En;
      rewrite evenb_S in En;
      apply (f_equal _ _ negb) in En;
      rewrite negb_involutive in En;
      rewrite En in H;
      simpl in H.
    + exists (S k). rewrite H. reflexivity.
    + exists k. rewrite H. reflexivity.
Qed.

Theorem even_bool_prop : forall n,
    evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k' H'].
    rewrite H in H'. exists k'. exact H'.
  - intros [k H]. rewrite H. apply evenb_double.
Qed.

Theorem beq_nat_true_iff: forall n1 n2 : nat,
    beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros E. rewrite E. symmetry. apply beq_nat_refl.
Qed.

Fail Definition is_even_prime n :=
  if n = 2 then true else false.

Example even_1000: exists k, 1000 = double k.
Proof. exists 500. reflexivity. Qed.

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

Example even_1000'': exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

(** *Exercise and_true_iff *)
Lemma andb_true_iff : forall b1 b2: bool,
    b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H. split.
    + destruct b1.
      * reflexivity.
      * inversion H.
    + destruct b2.
      * reflexivity.
      * destruct b1; inversion H.
  - intros [H1 H2]. rewrite H1, H2. reflexivity.
Qed.

Lemma orb_true_iff: forall b1 b2: bool,
    b1 || b2 = true -> b1 = true \/ b2 = true.
Proof.
  intros [|] [|]; simpl; intros H; try inversion H; try (left;reflexivity); try (right;reflexivity).
Qed.

(** *Exercise beq_nat_false_iff *)
Theorem beq_nat_false_iff : forall x y,
    beq_nat x y = false <-> x <> y.
Proof.
  intros x y. split.
  - intros H E. apply beq_nat_true_iff in E. rewrite H in E. inversion E.
  - intros H. destruct (beq_nat x y) eqn:E.
    + exfalso. apply H, beq_nat_true, E.
    + reflexivity.
Qed.

Fixpoint beq_list {A: Type} (beq: A -> A -> bool) (l1 l2: list A): bool :=
  match (l1, l2) with
  | ([] , []) => true
  | ([] , _::_) | (_::_, []) => false
  | (h1::t1, h2::t2) => beq h1 h2 && beq_list beq t1 t2
  end.

Lemma beq_list_true_iff: forall A (beq: A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
  intros A beq R l1 l2. generalize dependent l2.
  induction l1 as [|h1 t1 IH1]; destruct l2 as [|h2 t2]; split;
    intros H; try reflexivity; try (inversion H;fail); simpl in H.
  - rewrite andb_true_iff in H. destruct H as [H1 H2].
    apply R in H1. apply IH1 in H2.
    rewrite H1, H2. reflexivity.
  - simpl. rewrite andb_true_iff. split; [apply R|apply IH1]; inversion H; reflexivity.
Qed.
(** *Exercise All_forallb *)
Theorem forallb_true_iff : forall X test (l : list X),
    forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test. induction l as [|h t IH]; split; intro H; simpl; simpl in H; try reflexivity.
  - rewrite andb_true_iff in H. destruct H as [Hl Hr]. split.
    + exact Hl.
    + apply IH, Hr.
  - rewrite andb_true_iff. destruct H as [Hl Hr]. split.
    + exact Hl.
    + apply IH, Hr.
Qed.
(* forallb has short circuit behavior and can be tested in match *)

Definition excluded_middle := forall P: Prop, P \/ ~ P.
Theorem restricted_excluded_middle: forall P b,
    (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

Theorem restricted_excluded_middle_eq: forall (n m : nat), n = m \/ n <> m.
Proof.
  intros n m. apply (restricted_excluded_middle (n=m) (beq_nat n m)). symmetry.
  apply beq_nat_true_iff.
Qed.

(** *Exercise excluded_middle_irrefutable *)
Theorem excluded_middle_irrefutable: forall P: Prop, ~~(P \/ ~P).
Proof.
  intros P H. apply H. right. intro p. apply H. left. exact p.
Qed.

(** *Exercise not_exists_dist *)
Theorem net_exists_dist :
  excluded_middle -> forall (X: Type) (P: X -> Prop),
    ~ (exists x, ~ P x) -> forall x, P x.
Proof.
  intros Ex X P H x.
  destruct (Ex (P x)) as [H'|H'].
  - exact H'.
  - exfalso. apply H. exists x. exact H'.
Qed.

(** *Exercise classical_axioms *)
Definition pierce := forall P Q: Prop, ((P -> Q) -> P) -> P.
Definition double_negation_elimination := forall P: Prop, ~~P -> P.
Definition de_morgan_not_and_not := forall P Q: Prop, ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q : Prop, (P -> Q) -> (~P \/ Q).
Lemma excluded_middle_double_negation_elimination:
  excluded_middle <-> double_negation_elimination.
Proof.
  split; intros H.
  - intros P nnp. destruct (H P) as [H'|H'].
    + exact H'.
    + exfalso. apply nnp. exact H'.
  - intros P. apply H. apply excluded_middle_irrefutable.
Qed.
Lemma excluded_middle_pierce: excluded_middle <-> pierce.
Proof.
  split; intros H0.
  - intros P Q H1. destruct (H0 P) as [H2|H2].
    + exact H2.
    + apply H1. intros H3. exfalso. apply H2, H3.
  - intros P. apply (H0 (P \/ ~P) False). intros H1. exfalso.
    apply excluded_middle_irrefutable with P. exact H1.
Qed.
Lemma excluded_middle_de_morgan_not_and_not :
  excluded_middle <-> de_morgan_not_and_not.
Proof.
  split; intros H0.
  - intros P Q H1.
    destruct (H0 P) as [H2|H2]; destruct (H0 Q) as [H3|H3];
      try (left; exact H2); try (right; exact H3).
    exfalso. apply H1. split; [exact H2|exact H3].
  - intros P. apply H0. intros [H1 H2]. apply H2, H1.
Qed.
Lemma excluded_middle_implies_to_or:
  excluded_middle <-> implies_to_or.
Proof.
  split; intros H0.
  - intros P Q H1. destruct (H0 P) as [H2|H2].
    + right. apply H1, H2.
    + left. exact H2.
  - intros P. rewrite <- or_comm. apply H0. intro p; exact p.
Qed.
Theorem classical_axioms:
  (excluded_middle <-> pierce)
  /\ (pierce <-> double_negation_elimination)
  /\ (double_negation_elimination <-> de_morgan_not_and_not)
  /\ (de_morgan_not_and_not <-> implies_to_or).
Proof.
  rewrite <- excluded_middle_de_morgan_not_and_not.
  rewrite <- excluded_middle_pierce.
  rewrite <- excluded_middle_double_negation_elimination.
  rewrite <- excluded_middle_implies_to_or.
  assert (L: forall P, P <-> P).
  { intro P. split; intro p; exact p. }
  split. apply L. split. apply L. split. apply L. apply L.
Qed.