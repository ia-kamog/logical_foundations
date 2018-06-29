Set Warnings "-notation-overriden,-parsing".
Require Export Lists.

Inductive boollist : Type :=
| bool_nil : boollist
| bool_cons : bool -> boollist -> boollist.
Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.
Check list.
Check (nil nat).
Check (cons nat 3 (nil nat)).
Check nil.
Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1: repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.
Example test_repeat2: repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.
  (** *Exercise mumble_grumble *)
  Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
  Inductive grumble (X:Type): Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

  (* Check d (b a 5). *)
  Check d mumble (b a 5).
  Check d bool (b a 5).
  Check e bool true.
  Check e mumble (b c 0).
  (* Check e bool (b c 0). *)
  (* c *)
End MumbleGrumble.

Fixpoint repeat' X x count :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'.
Check repeat.

Fixpoint repeat'' X x count : list X :=
  match count with
  | O => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.
Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

Inductive list' {X:Type} : Type :=
| nil' : list'
| cons' : X -> list' -> list'.
Check cons' 1 nil'.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
Fixpoint length {X: Type} (l: list X): nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.
Example test_rev1:
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.
Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.
Example test_length: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.
Fail Definition mynil := nil.
Definition mynil : list nat := nil.
Check @nil.
Definition mynil' := @nil nat.
Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).
Definition list123''' := [1;2;3].

(** *Exercise poly_exercises *)
Theorem app_nil_r: forall (X:Type)(l: list X), l ++ [] = l.
Proof.
  intros X l. induction l as [|x l' I].
  - reflexivity.
  - simpl. rewrite -> I. reflexivity.
Qed.
Theorem app_assoc: forall A (l m n: list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n. induction l as [|x l' I].
  - reflexivity.
  - simpl. rewrite -> I. reflexivity.
Qed.

Lemma app_length: forall (X: Type) (l1 l2: list X),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros x l1 l2. induction l1 as [|h t I].
  - reflexivity.
  - simpl. rewrite -> I. reflexivity.
Qed.

(** *Exercise more_poly_exercises *)
Theorem rev_app_distr: forall X (l1 l2: list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [|h t I].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> app_assoc, -> I. reflexivity.
Qed.
Theorem rev_involutive: forall X: Type, forall l: list X,
      rev (rev l) = l.
Proof.
  intros X l. induction l as [|h t I].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr, -> I. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.
Arguments pair {X} {Y} _ _.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y: Type} (p: X*Y): X :=
  match p with
  | (x, _) => x
  end.
Definition snd {X Y: Type} (p: X*Y): Y :=
  match p with
  | (x, y) => y
  end.
Fixpoint combine {X Y: Type} (lx: list X) (ly: list Y)
  : list (X*Y) :=
  match lx, ly with
  | [], _ | _, [] => []
  | x::tx, y::ty => (x,y) :: (combine tx ty)
  end.
(** *Exercise combine_checks *)
(* @combine: forall (X Y: Type), list X -> list Y -> list (X*Y) *)
Check @combine.
(* combine [1;2] [false; false; true; true] = [(1,false);(2; false)] *)
Compute (combine [1; 2] [false; false; true; true]).

Fixpoint split {X Y: Type} (l: list (X*Y))
  : (list X) * (list Y) :=
  match l with
  | [] => ([],[])
  | (x, y) :: t =>
    match split t with
    | (lx, ly) => (x::lx, y::ly)
    end
  end.
Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Inductive option (X: Type): Type :=
| Some: X -> option X
| None: option X.
Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X: Type} (l: list X) (n: nat): option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
  end.
Example test_nth_error1: nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2: nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3: nth_error [true] 2 = None.
Proof. reflexivity. Qed.
(** *Exercise hd_error_poly *)
Definition hd_error {X: Type} (l: list X): option X :=
  match l with
  | [] => None
  | h :: _ => Some h
  end.
Check @hd_error.
Example test_hd_error1: hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2: hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.
