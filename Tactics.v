Set Warnings "-notation-overriden,-parsing".
Require Export Poly.
Theorem silly1: forall (n m o p: nat),
    n = m ->
    [n;o] = [n;p] ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2. rewrite <- eq1. apply eq2. Qed.
Theorem silly2: forall (n m o p: nat),
    n = m ->
    (forall (q r: nat), q = r -> [q;o] = [r;p]) ->
    [n;o] = [m;p].
Proof. intros n m o p eq1 eq2. apply eq2. apply eq1. Qed.
Theorem silly2a: forall (n m : nat),
    (n, n) = (m, m) ->
    (forall (q r: nat), (q, q) = (r, r) -> [q] = [r]) ->
    [n] = [m].
Proof. intros n m eq1 eq2. apply eq2. apply eq1. Qed.
(** *Exercise silly_ex *)
Theorem silly_ex:
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true -> oddb 4 = true.
Proof. intros H1 H2. apply H1. apply H2. Qed.
Theorem silly3_firsttry: forall (n: nat),
    true = beq_nat n 5 -> beq_nat (S (S n)) 7 = true.
Proof. intros n H. symmetry. simpl. apply H. Qed.
(** *Exercise apply_exercise1 *)
Theorem rev_exercise1: forall (l l': list nat),
    l = rev l' -> l' = rev l.
Proof. intros l l' H. rewrite -> H. symmetry. apply rev_involutive. Qed.
(** *Exercise apply_rewrite
    apply is a tool to match the target against a consequent of a statement.
    rewrite performs substitution if the target and the consequent are
    equalities. *)
Example trans_eq_example: forall (a b c d e f: nat),
    [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof. intros a b c d e f eq1 eq2. rewrite -> eq1, -> eq2. reflexivity. Qed.
Theorem trans_eq: forall (X:Type) (n m o:X),
    n = m -> m = o -> n = o.
Proof. intros X n m o eq1 eq2. rewrite -> eq1, -> eq2. reflexivity. Qed.
Example trans_eq_example': forall a b c d e f : nat,
    [a;b]=[c;d] -> [c;d]=[e;f] -> [a;b]=[e;f].
Proof.
  intros a b c d e f eq1 eq2. apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2. Qed.
(** *Exercise apply_with_exercise *)
Example trans_eq_exercise: forall n m o p: nat,
    m = minustwo o -> n + p = m -> n + p = minustwo o.
Proof. intros n m o p eq1 eq2. apply trans_eq with m. apply eq2. apply eq1. Qed.

Theorem S_injective: forall n m : nat, S n = S m -> n = m.
Proof. intros n m H. inversion H. reflexivity. Qed.

Theorem inversion_ex1: forall n m o: nat,
    [n;m]=[o;o] -> [n]=[m].
Proof. intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2: forall n m: nat, [n] = [m] -> n = m.
Proof. intros n m H. inversion H as [Hnm]. reflexivity. Qed.

(** *Exercise inversion_ex3 *)
Example inversion_ex3: forall(X: Type)(x y z: X) (l j: list X),
    x::y::l = z::j -> y::l = x::j -> x = y.
Proof.
  intros X x y z  l j eq1 eq2. inversion eq2. reflexivity. Qed.
Theorem beq_nat_0_l: forall n, beq_nat 0 n = true -> n = 0.
Proof.
  destruct n as [| n'].
  - intros H. reflexivity.
  - simpl. intros H. inversion H. Qed.
Theorem inversion_ex4: forall n, S n = O -> 2 + 2 = 5.
Proof. intros n contra. inversion contra. Qed.
Theorem inversion_ex5: forall n m: nat, false = true -> [n] = [m].
Proof. intros n m contra. inversion contra. Qed.
(** *Exercise inversion_ex6 *)
Example inversion_ex6: forall(X: Type)(x y z: X)(l j: list X),
    x::y::l = [] -> y::l=z::j -> x = z.
Proof. intros X x y z l j H. inversion H. Qed.

Theorem f_equal: forall (A B: Type)(f: A -> B)(x y: A),
    x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem S_inj: forall (n m: nat)(b: bool), beq_nat (S n) (S m) = b -> beq_nat n m = b.
Proof. intros n m b H. simpl in H. apply H. Qed.
Theorem silly3': forall n: nat,
    (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
    true = beq_nat n 5 -> true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H. symmetry in H. apply eq in H. symmetry in H. apply H. Qed.
(** *Exercise plus_n_n_injectie *)
Theorem plus_n_n_injective: forall n m, n + n = m + m -> n = m.
Proof.
  intros n. induction n as [| n' I].
  - destruct m as [|m'].
    + intros _. reflexivity.
    + intros H. inversion H.
  - intros m H. destruct m as [|m'].
    + inversion H.
    + rewrite <- ?plus_n_Sm in H. simpl in H. inversion H as [H'].
      apply I in H'. rewrite H'. reflexivity. Qed.

Theorem double_injective_FAILED: forall n m, double n = double m -> n = m.
Proof.
  intros n m. induction n as [|n'].
  - simpl. intros eq. destruct m as [|m'].
    + reflexivity.
    + inversion eq.
  - intros eq. destruct m as [|m'].
    + inversion eq.
    + apply f_equal.
Abort.
Theorem double_injective: forall n m, double n = double m -> n = m.
Proof.
  intros n. induction n as [|n' I].
  - simpl. intros m eq. destruct m as [|m'].
    + reflexivity.
    + inversion eq.
  - simpl. intros m eq. destruct m as [|m'].
    + simpl. inversion eq.
    + apply f_equal. apply I. inversion eq. reflexivity. Qed.
(** *Exercise beq_nat_true *)
Theorem beq_nat_true: forall n m, beq_nat n m = true -> n = m.
Proof.
  induction n as [|n I].
  - destruct m as [|m].
    + reflexivity.
    + intros c. inversion c.
  - simpl. destruct m as [|m].
    + intros c. inversion c.
    + intros H. apply f_equal. apply I. apply H.
Qed.
(** *Exercise beq_nat_true_informal
We need to prove forall n m, beq_nat n m = true -> n = m.
Proceed by induction on n:
if n = 0, then forall m, beq_nat 0 m = true -> 0 = m is obvious.
Assume, forall m, plus n m = true -> n = m. Then for S n we need to prove
forall m, beq_nat (S n) m = true -> S n = m.
It is sufficient to consider m of the form S _, since the antecedent is false
otherwise.
Thus, it simplifies to forall m, beq_nat n m -> n = m, which is the assumption.
*)

Theorem double_injective_take2: forall n m, double n = double m -> n = m.
Proof.
  intros n m. generalize dependent n.
  induction m as [|m']; destruct n as [|n']; intros H.
  - reflexivity.
  - inversion H.
  - inversion H.
  - apply f_equal. simpl in H. inversion H as [H1]. apply IHm' in H1. exact H1.
Qed.

Theorem beq_id_true: forall x y, beq_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H': m = n).
  { apply beq_nat_true. apply H. }
  rewrite H'. reflexivity.
Qed.

(** *Exercise gen_dep_practice *)
Theorem nth_error_after_last: forall (n: nat)(X: Type)(l: list X),
    length l = n -> nth_error l n = None.
Proof.
  intros n X l. generalize dependent n.
  induction l as [|h t I]; intros n H.
  - reflexivity.
  - simpl in H. destruct n as [|n].
    + inversion H.
    + simpl. apply I. inversion H. reflexivity.
Qed.

Definition square n := n * n.
Lemma square_mult: forall n m, square (n * m) = square n * square m.
Proof.
  intros n m. simpl. unfold square.
  rewrite mult_assoc.
  assert (H: n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity. Qed.

Definition foo (x: nat) := 5.
Fact silly_fact_1: forall m, foo m + 1 = foo (m+1)+1.
Proof. intros m. simpl. reflexivity. Qed.
Definition bar x :=
  match  x with
  | O => 5
  | S _ => 5
  end.
Fact silly_fact_2_FAILED: forall m, bar m + 1 = bar (m + 1) + 1.
Proof. intros m. simpl. Abort.
Fact silly_fact_2: forall m, bar m + 1 = bar (m + 1) + 1.
Proof. destruct m; reflexivity. Qed.
Fact silly_fact_2': forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m. unfold bar. destruct m; reflexivity. Qed.

Definition sillyfun (n: nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
       else false.

Theorem silly_fun_false: forall(n:nat), sillyfun n = false.
Proof. intros n. unfold sillyfun. destruct (beq_nat n 3).
       - reflexivity.
       - destruct (beq_nat n 5); reflexivity.
Qed.
(** *Exercise combine_split *)
Fixpoint split {X Y: Type} (l: list (X*Y)): (list X)*(list Y) :=
  match l with
  | [] => ([],[])
  | (x,y) :: t =>
    match split t with
    | (lx, ly) => (x::lx, y::ly)
    end
  end.
Theorem combine_split: forall X Y (l: list (X*Y)) l1 l2,
    split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| h t I]; intros l1 l2 H.
  - simpl in H. inversion H. reflexivity.
  - simpl in H. destruct h as [x y].
    destruct (split t) as [lx ly]. inversion H. simpl.
    apply f_equal. apply I. reflexivity.
Qed.
Definition sillyfun1 (n:nat):bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
       else false.
Theorem sillyfun1_odd_FAILED: forall n:nat,
    sillyfun1 n = true -> oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3). Abort.
Theorem sillyfun1_odd: forall n:nat, sillyfun1 n = true -> oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  - apply beq_nat_true in Heqe3. rewrite -> Heqe3. reflexivity.
  - destruct (beq_nat n 5) eqn:Heqe5.
    + apply beq_nat_true in Heqe5. rewrite Heqe5. reflexivity.
    + inversion eq. Qed.
(** *Exercise destruct_eqn_practice *)
Theorem bool_fn_applied_thrice:
  forall (f: bool -> bool) (b: bool), f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b eqn:eb; destruct (f true) eqn:eqf1;
    destruct (f false) eqn:eqf2; rewrite ?eqf1; rewrite ?eqf2;
      try reflexivity.
Qed.

(** *Exercise beq_nat_sym *)
Theorem beq_nat_sym: forall n m, beq_nat n m = beq_nat m n.
Proof.
  induction n as [|n I]; intros m.
  - simpl. destruct m; reflexivity.
  - simpl. destruct m.
    + reflexivity.
    + simpl. apply I.
Qed.

(** *Exercise beq_nat_sym_informal
Theorem: for any n m, beq_nat n m = beq_nat m n.
Use induction on n.
* First we need to prove for any m, beq_nat 0 m = beq_nat m 0.
  beq_nat 0 m is true if m is 0 and false if m = S m'. Considering both
  cases let's reduce beq_nat m 0. So, it follows.
* Prove for any m, beq_nat (S n') m = beq_nat m (S n'), if we know
  that for any m, beq_nat n' m = beq_nat m n'.
  Consider cases for m:
  * m = 0, then both parts evaluate to false.
  * m = S m', then beq_nat (S n') (S m') reduces to beq_nat n' m' and
    beq_nat (S m') (S n') reduces to beq_nat m' n', thus giving the assumption.
 *)

(** *Exercise beq_nat_trans *)
Theorem beq_nat_trans: forall n m p,
    beq_nat n m = true -> beq_nat m p = true -> beq_nat n p = true.
Proof.
  intros n m p H1 H2. apply beq_nat_true in H1. rewrite -> H1. apply H2. Qed.

(** *Exercise split_combine *)
Definition split_combine_statement: Prop :=
  forall (X Y: Type)(l1: list X)(l2: list Y),
    length l1 = length l2 -> split (combine l1 l2) = (l1,l2).
Theorem split_combine: split_combine_statement.
Proof.
  intros X Y. induction l1 as [|h1 t1 I]; intros l2 H.
  - destruct l2 as [|h2 t2].
    + reflexivity.
    + inversion H.
  - destruct l2 as [|h2 t2].
    + inversion H.
    + simpl in H. inversion H as [H']. apply I in H'. simpl.
      rewrite H'. reflexivity.
Qed.

(** *Exercise filter_exercise *)
Theorem filter_exercise: forall (X:Type)(test:X->bool)(x:X)(l lf:list X),
    filter test l = x :: lf -> test x = true.
Proof.
  intros X test x l. induction l as [|h t I]; intros lf H.
  - inversion H.
  - simpl in H. destruct (test h) eqn:e.
    + inversion H as [H']. rewrite H' in e. apply e.
    + apply I in H. exact H.
Qed.

(** *Exercise forall_exists_challenge *)
Fixpoint forallb {X: Type}(p: X -> bool)(l: list X): bool :=
  match l with
  | [] => true
  | h::t => p h && forallb p t
  end.
Fixpoint existb {X: Type}(p: X -> bool)(l: list X): bool :=
  match l with
  | [] => false
  | h::t => p h || existb p t
  end.

Example forallb_test1: forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example forallb_test2: forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example forallb_test3: forallb evenb [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example forallb_test4: forallb (beq_nat 5) [] = true.
Proof. reflexivity. Qed.

Example existb_test1: existb (beq_nat 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example existb_test2: existb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example existb_test3: existb oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example existb_test4: existb evenb [] = false.
Proof. reflexivity. Qed.

Definition existb' {X:Type}(p: X -> bool)(l: list X) :=
  negb (forallb (fun x => negb (p x)) l).

Theorem existb_existb': forall (X: Type)(p: X -> bool)(l: list X),
    existb p l = existb' p l.
Proof.
  intros X p. induction l as [|h t I].
  - reflexivity.
  - unfold existb'. simpl. destruct (p h) eqn:eqn1; simpl.
    + reflexivity.
    + apply I.
Qed.