(* 
   That's a bad code. Go away! 
   You may not view it, if you participate in a course using the textbook.
*)

Inductive day : Type :=
| monday   : day
| tuesday  : day
| wednesday: day
| thursday : day
| friday   : day
| saturday : day
| sunday   : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool := negb (b1 && b2).
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (b1 && b2) && b3.
Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Check true.
Check (negb true).
Check negb.

Inductive rgb: Type :=
| red   : rgb
| green : rgb
| blue  : rgb.

Inductive color : Type :=
| black  : color
| white  : color
| primary: rgb -> color.

Definition monochrome (c:color): bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition israd (c:color): bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Module NatPlayground.
  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.
  Inductive nat' : Type :=
  | stop : nat'
  | tick : nat' -> nat'.
  Definition pred (n:nat): nat :=
    match n with
    | O => O
    | S n' => n'
    end.
End NatPlayground.

Check (S (S (S (S O)))).
Definition minustwo (n:nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
Compute (minustwo 4).
Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat): bool := negb (evenb n).
Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.
  Compute (plus 3 2).

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

  Example test_mult1: (mult 3 3) = 9.
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus (n m: nat) : nat :=
    match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
    end.
End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => mult n (factorial n')
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                    : nat_scope.
Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                    : nat_scope.
Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                    : nat_scope.
Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
        | O => true
        | S _ => false
        end
  | S n' => match m with
           | O => false
           | S m' => beq_nat n' m'
           end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
    match m with
    | O => false
    | S m' => leb n' m'
    end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  negb (beq_nat n m) && leb n m.
Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_O_n: forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity.
Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof. intros n. simpl. reflexivity. Qed.
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof. intros n. simpl. reflexivity. Qed.


Theorem plus_id_example : forall n m:nat,
    n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o H1 H2.
  rewrite <- H2.
  rewrite -> H1.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
    (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
    m = S n ->
    m * (1 + n) = m * m.
Proof.
  intros n m H.
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_1_neq_0: forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive: forall b:bool,
    negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative: forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, b && c = c && b.
Proof.
  intros b c. destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem plus_1_neq_0' : forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'':
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim: forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros b c. rewrite -> andb_commutative. intros H. destruct c.
  - reflexivity.
  - rewrite <- H. reflexivity.
Qed.

Theorem zero_nbeq_plus_1: forall n : nat,
    beq_nat 0 (n + 1) = false.
Proof.
  intros [|n].
  - reflexivity.
  - simpl. reflexivity.
Qed.

(*
Fixpoint div (n m : nat) : nat :=
  match n with
  | O => O
  | S _ => S (div (minus n m) m)
  end.
 *)

Theorem indentitiy_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = x) ->
    forall (b : bool), f (f b) = b.
Proof.
  intros f H b. rewrite -> H. rewrite -> H. reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
    (b && c = b || c) ->
    b = c.
Proof.
  intros b c. destruct b; simpl; intros H; rewrite -> H; reflexivity.
Qed.
(* 3.a *)
Inductive bin : Type :=
| Zero : bin
| Double : bin -> bin
| Double_Plus_One : bin -> bin.
(* b *)
Fixpoint incr (n : bin) : bin :=
  match n with
  | Zero => Double_Plus_One n
  | Double n' => Double_Plus_One n'
  | Double_Plus_One n' => Double (incr n')
  end.
Fixpoint bin_to_nat (n: bin) :=
  match n with
  | Zero => O
  | Double n' => 2 * (bin_to_nat n')
  | Double_Plus_One n' => 1 + 2 * (bin_to_nat n')
  end.
(* c *)
Example test_bin_incr1: (bin_to_nat (incr (incr (incr Zero)))) = 3.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2: (bin_to_nat (incr (incr (Double (Zero))))) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3: S (bin_to_nat (Double  (Double_Plus_One Zero))) = bin_to_nat (incr (Double (incr Zero))).
Proof. simpl. reflexivity. Qed.