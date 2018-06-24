Require Export Induction.
Module NatList.
  Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.
  Check (pair 3 5).
  Definition fst (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.
  Definition snd (p:natprod) : nat :=
    match p with
    | pair x y => y
    end.
  Compute (fst (pair 3 5)).
  Notation "( x , y )" := (pair x y).
  Compute (fst (3,5)).
  Definition fst' (p:natprod) : nat :=
    match p with
    | (x,y) => x
    end.
  Definition snd' (p:natprod) : nat :=
    match p with
    | (x,y) => y
    end.
  Definition swap_pair (p:natprod) : natprod :=
    match p with
    | (x,y) => (y,x)
    end.
  Theorem surjective_pairing': forall (n m : nat),
      (n,m) = (fst (n, m), snd (n, m)).
  Proof.
    reflexivity.
  Qed.

  Theorem surjective_pairing_stuck : forall (p : natprod),
      p = (fst p, snd p).
  Proof.
    simpl.
  Abort.
  Theorem surjective_pairing : forall (p : natprod),
      p = (fst p, snd p).
  Proof.
    intros p. destruct p as [n m]. simpl. reflexivity. Qed.

  (** *Exercise snd_fst_is_swap *)
  Theorem snd_fst_is_swqpa : forall p:natprod,
      (snd p, fst p) = swap_pair p.
  Proof.
    destruct p as [n m]. reflexivity. Qed.
  (** *Exercise fst_sqap_is_snd *)
  Theorem fst_swap_is_snd : forall p:natprod,
      fst (swap_pair p) = snd p.
  Proof. destruct p as [m n]. reflexivity. Qed.

  Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

  Definition mylist := cons 1 (cons 2 (cons 3 nil)).
  Notation "x :: l" := (cons x l) (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  Definition myList1 :=  1 :: (2 :: (3 :: nil)).
  Definition myList2 := 1 :: 2 :: 3 :: nil.
  Definition myList3 := [1;2;3].
  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => nil
    | S count' => n :: (repeat n count')
    end.
  Fixpoint length (l:natlist) : nat :=
    match l with
    | nil => O
    | h :: t => S (length t)
    end.
  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.
  Notation "x ++ y" := (app x y) (right associativity, at level 60).
  Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
  Proof. reflexivity. Qed.
  Example test_app2: nil ++ [4;5] = [4;5].
  Proof. reflexivity. Qed.
  Example test_app3: [1;2;3] ++ nil = [1;2;3].
  Proof. reflexivity. Qed.

  (** *Exercise list_funs *)
  Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => match h with
               | O => nonzeros t
               | S _ => h :: nonzeros t
               end
    end.
  Example test_nonzeros:
    nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. reflexivity. Qed.
  Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
    | [] => []
    | h :: t => match oddb h with
               | true => h :: oddmembers t
               | false => oddmembers t
               end
    end.
  Example test_oddmembers:
    oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. reflexivity. Qed.
  Definition countoddmembers (l:natlist) := length (oddmembers l).
  Example test_countoddmembers1:
    countoddmembers [1;0;3;1;4;5] = 4.
  Proof. reflexivity. Qed.
  Example test_countoddmembers2:
    countoddmembers [0;2;4] = 0.
  Proof. reflexivity. Qed.
  Example test_countoddmembers3:
    countoddmembers nil = 0.
  Proof. reflexivity. Qed.

  (** *Exercise alternate *)
  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1,l2 with
    | [],[] => nil
    | [], _ => l2
    | _, [] => l1
    | h1::t1, h2::t2 => h1::h2::(alternate t1 t2)
    end.
  Example test_alternate1:
    alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. reflexivity. Qed.
  Example test_alternate2:
    alternate [1] [4;5;6] = [1;4;5;6].
  Proof. reflexivity. Qed.
  Example test_alternate3:
    alternate [1;2;3] [4] = [1;4;2;3].
  Proof. reflexivity. Qed.
  Example test_alternate4:
    alternate [] [20;30] = [20;30].