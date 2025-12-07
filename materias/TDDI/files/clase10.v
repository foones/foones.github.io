
Require Import Lia.

(* Rocq proof assistant *)

Inductive natural :=
  cero : natural
| suc  : natural -> natural.

Definition enunciado_teorema1 : Prop :=
  forall X : Prop, X -> X.

Theorem teorema1 : enunciado_teorema1.
  intro.
  intro.
  assumption.
Qed.

Theorem teorema2 : forall n m : nat,
                      (n + m) * m <> m * m + m * n + 1.
  lia.
Qed.

Proposition conj_conmutativa : forall P Q : Prop,
                                  P /\ Q -> Q /\ P.
Proof.
  intros P Q [H1 H2].
  split.
  - apply H2.
  - apply H1.
Qed.

Proposition disy_conmutativa : forall P Q : Prop,
                                  P \/ Q -> Q \/ P.
  intros P Q [H1 | H2].
  - right.
    apply H1.
  - left.
    apply H2.
Qed.

Inductive List : Set :=
    nil : List
  | cons : nat -> List -> List.

Check cons 1 (cons 2 nil).

Fixpoint length (xs : List) : nat :=
  match xs with
  | nil       => O
  | cons _ ys => S (length ys)
  end.

Fixpoint append (xs ys : List) : List :=
  match xs with
  | nil       => ys
  | cons z zs => cons z (append zs ys)
  end.

Check (forall (n : nat), n = O).
Check nat.
(*
Fixpoint div (n m : nat) (p : not (m = O)) : nat :=
  match 
*)
