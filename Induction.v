Require Export Basics.
Theorem plus_n_O_firsttry : forall n : nat,
    n = n + 0.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_n_O_secondtry : forall n:nat,
    n = n + 0.
Proof.
  intros n. destruct n as [|n'].
  - reflexivity.
  - simpl.
Abort.

Theorem plus_n_O: forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n, minus n n = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(** *Exercise: basic_induction *)
Theorem mult_0_r : forall n:nat, n * 0 = 0.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. exact IHn'.
Qed.

Theorem plus_n_Sm: forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  induction m as [| m' IHm'].
  - rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite <- plus_n_Sm, -> IHm'. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(** *Exercise: double_plus *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite <- plus_n_Sm, -> IHn'. reflexivity.
Qed.

(* Exercise evenb_S *)
Theorem evenb_S : forall n : nat, evenb (S n) = negb (evenb n).
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - rewrite -> IHn', negb_involutive. reflexivity.
Qed.


(** *Exercise: destruct_induction
    Let there be an inductive Type T constructed by C^i_j.
    destruct on term t will add a goal for each constructor.
    intduction will add a goal for each constructor together
    with hypotheses that state to each T argument of the constructor.

    So, destruct is restricted induction that can be used to prove
    statements about T that don't depend on the truth of the statement
    for each argument of the constructor. *)

Theorem mult_0_plus': forall n m : nat,
    (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
  { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite -> plus_comm.
Abort.

Theorem plus_rearrage: forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.

Theorem plus_assoc': forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn' ]. reflexivity.
  simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_assoc'': forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn' ].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

(** *Exercise plus_comm_informal
    Forall n, m : nat, n + m = m + n.
    By induction on n:
    n = 0: 0 + m = m + 0.
      by definition of +: m = m + 0.
      By induction on m:
      m = 0: 0 = 0
      m = S m': Suppose m' + 0 = m', then
        S (m' + 0) = S m', by definition of +, it's the same as
        (S m') + 0 = S m', or m + 0 = 0.
    n = S n': S n' + m = m + S n' given n' + m = m + n'.
      Let's prove m + S n' = S (m + n') by induction on m.
      m = 0 is obvious.
      assume m = S m' and m' + S n' = S (m' + n'), then S m' + S n' =
      = S (m' + S n') = S (S (m' + n')) = S (S m' + n').
      m + S n' = S (m + n') = S (n' + m) = S n' + m, proving the assertion.
 *)

Print beq_nat.

(** *Exercise beq_nat_refl_informal
    true = beq_nat n n.
    Prove by induction on n.
    If n = 0, then beq_nat simplifies to truth.
    If n = S n', then it follows from beq_nat n' n'. *)

(* Exercise mult_comm *)
Theorem plus_swap : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p. assert (H: n + (m + p) = (n + m) + p).
  { rewrite -> plus_assoc. reflexivity. }
  rewrite -> H.
  assert (H': n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H'.
  assert (H'': m + (n + p) = m + n + p).
  { rewrite -> plus_assoc. reflexivity. }
  rewrite -> H''.
  reflexivity.
Qed.

Theorem mult_n_Sm : forall n m : nat,
    n * S m = n + n * m.
Proof.
  intros n m.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite -> IHn, -> plus_swap. reflexivity.
Qed.
Theorem mult_comm : forall m n: nat,
    m * n = n * m.
Proof.
  intros n m. induction n as [| n' IHn' ].
  - simpl. rewrite -> mult_0_r. reflexivity.
  - simpl. rewrite -> mult_n_Sm, -> IHn'. reflexivity.
Qed.

(* Exercise: more_exercises *)

Check leb.

Theorem leb_refl : forall n : nat, true = leb n n.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. exact IHn.
Qed.

Theorem zero_nbeq_S : forall n : nat, beq_nat 0 (S n) = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool, b && false = false.
Proof.
  destruct b; reflexivity.
Qed.

Theorem plus_ble_compat_l: forall n m p : nat,
    leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros n m p H. induction p as [| p IHp ].
  - simpl. exact H.
  - simpl. exact IHp.
Qed.

Theorem S_nbeq_0 : forall n : nat, beq_nat (S n) 0 = false.
Proof. intros n. reflexivity. Qed.

Theorem mult_1_l : forall n:nat, 1*n = n.
Proof. intros n. simpl. rewrite <- plus_n_O. reflexivity. Qed.

Theorem all3_spec: forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
           (negb c))
    = true.
Proof.
  intros b c. destruct b; simpl; destruct c; reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat, (n + m) * p = n * p + m * p.
Proof.
  intros n m p. induction n as [|n IHn].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn. rewrite -> plus_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat, n*(m*p) = (n*m)*p.
Proof.
  intros n m p. induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite -> mult_plus_distr_r, -> IHn. reflexivity.
Qed.

(** *Exercise beq_nat_refl *)
Theorem beq_nat_refl : forall n : nat, true = beq_nat n n.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. exact IHn.
Qed.

(** *Exercise plus_swap' *)
Theorem plus_swap': forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p. replace (n+(m+p)) with ((n+m)+p).
  replace (n+m) with (m+n).
  - rewrite -> plus_assoc. reflexivity.
  - rewrite -> plus_comm. reflexivity.
  - rewrite -> plus_assoc. reflexivity.
Qed.

(** *Exercise binary_commute *)

Theorem bin_to_nat_pres_incr : forall b : bin, bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b. induction b as [| b IHb | b IHb ].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite -> IHb, <- plus_n_Sm. reflexivity.
Qed.

(** *Exercise binary_inverse *)
Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | O => Zero
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_to_bin_l_inv:
  forall n : nat, bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite -> bin_to_nat_pres_incr. rewrite -> IHn. reflexivity.
Qed.

Fixpoint bin_zero (b : bin) : bool :=
  match b with
  | Zero => true
  | Double b' => bin_zero b'
  | Double_Plus_One b' => false
  end.

Fixpoint normalize (b : bin) : bin :=
  match bin_zero b with
  | false => match b with
            | Zero => Zero
            | Double b' => Double (normalize b')
            | Double_Plus_One b' => Double_Plus_One (normalize b')
            end
  | true => Zero
  end.

Theorem binary_inverse: forall b : bin,
    nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  induction b as [|b Ib|b Ib].
  - reflexivity.
  - simpl. destruct (bin_zero b) eqn:Z.
    + assert (L: forall b', bin_zero b' = true -> bin_to_nat b' = 0).
      { intros b' H. induction b' as [|b' I'|b' I'].
        - reflexivity.
        - simpl. rewrite -> I'; [reflexivity | exact H].
        - simpl. inversion H. }
      rewrite -> L.
      * reflexivity.
      * exact Z.
    + assert (L1: forall n:nat, beq_nat n 0 = false ->
                         nat_to_bin (n+n) = Double (nat_to_bin n)).
      { intros n H. induction n as [|n I].
        - inversion H.
        - rewrite <- plus_n_Sm. simpl. destruct n as [|n'].
          + reflexivity.
          +  rewrite <- plus_n_Sm. rewrite <- plus_n_Sm in I. simpl.
             simpl in I. rewrite -> I.
             * reflexivity.
             * reflexivity. }
      rewrite -> L1. rewrite -> Ib. reflexivity.
      assert (L2 : forall x, bin_zero x = false ->
                        beq_nat (bin_to_nat x) 0 = false).
      { intros x H. induction x as [|x I|x I].
        - inversion H.
        -  simpl. simpl in H. destruct (bin_to_nat x).
           + apply I in H. inversion H.
           + rewrite <- plus_n_Sm. simpl. reflexivity.
        - reflexivity. }
      apply L2. exact Z.
  - simpl. rewrite <- Ib.
    assert (L: forall n:nat, incr (nat_to_bin (n+n)) =
                      Double_Plus_One (nat_to_bin n)).
    { induction n as [|n I].
      - reflexivity.
      - rewrite <- plus_n_Sm. simpl. rewrite -> I. reflexivity. }
    apply L.
Qed.