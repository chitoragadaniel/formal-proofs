Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-intuition-auto-with-star".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Import Hoare.
From PLF Require Import Hoare2.
Set Default Goal Selector "!".

Open Scope dcom_scope.


Definition FILL_IN_HERE := <{True}>.


(* ================================================================= *)
(** ** Exercise: Two Loops *)

Definition two_loops_dec (a b c : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ c = c }}
      X := 0
                   {{ c = X + c }};
      Y := 0
                   {{ c = X + Y + c }};
      Z := c
                   {{ Z = X + Y + c }};
      while X <> a do
                   {{ Z = X + Y + c /\ X <> a }} ->>
                   {{ (Z + 1) = (X + 1) + Y + c }}
        X := X + 1
                   {{ (Z + 1) = X + Y + c }};
        Z := Z + 1
                   {{ Z = X + Y + c }}
      end
                   {{ Z = X + Y + c /\ ~(X <> a) }} ->>
                   {{ Z = X + Y + c /\ X = a }};
      while Y <> b do
                   {{ Z = X + Y + c /\ X = a /\ Y <> b }} ->>
                   {{ (Z + 1) = X + (Y + 1) + c /\ X = a  }}
        Y := Y + 1
                   {{ (Z + 1) = X + Y + c /\ X = a}};
        Z := Z + 1
                   {{ Z = X + Y + c /\ X = a}}
      end
    {{ Z = X + Y + c /\ X = a /\ ~(Y <> b) }} ->>
    {{ Z = a + b + c }}
  }>.

Theorem two_loops : forall a b c,
  outer_triple_valid (two_loops_dec a b c).
Proof.
  verify.
Qed.
