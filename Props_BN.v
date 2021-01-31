Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Arith.
Require Import ArithRing.
Require Import Setoid.
Require Import Omega.
From Tarea3VF Require Import Defs_BN .
(* (*Datatype for our numerical system with 0, U and D*)
Inductive BN :=
  Z: BN
| U: BN -> BN
| D: BN -> BN.

Check BN_ind.
Check BN_rec.
Check BN_rect. *)

Lemma UInj: forall (a b:BN), U a = U b -> a = b.
Proof.
intros.
inversion H.
trivial.
Qed.

Lemma DInj: forall (a b:BN), D a = D b -> a = b.
Proof.
intros.
inversion H.
trivial.
Qed.


Lemma ZnotU: forall (a:BN), Z <> U a.
Proof.
intros.
discriminate.
Qed.

Lemma ZnotD: forall (a:BN), Z <> D a.
Proof.
intros.
discriminate.
Qed.

  (* Lemma UnotD: forall (a:BN), U a <> D a. La cambié por la siguiente. C.V. 29/nov/2016 *)
Lemma UnotD: forall (a b:BN), U a <> D b.
Proof.
intros.
discriminate.
Qed.

Lemma DnotU: forall (a b:BN), D a <> U b. (* La agregué. C.V. 29/nov/2016 *)
Proof.
intros.
discriminate.
Qed.

Lemma bnotU : forall (a:BN), U a <> a.
Proof.
intros.
induction a.
(*a = Z*)
intuition.
inversion H.
(*a=U a*)
intuition.
inversion H.
apply IHa in H1.
trivial.
(*a=D a*)
intuition.
inversion H.
Qed.

Lemma bnotD : forall (a:BN), D a <> a.
Proof.
intros.
induction a.
(*a = Z*)
intuition.
inversion H.
(*a=U a*)
intuition.
inversion H.
(*a=D a*)
intuition.
inversion H.
apply IHa in H1.
trivial.
Qed.

Theorem dec_eq_BN: forall (a b:BN), {a = b} + {a <> b}.
Proof. (* This can be done fully automatic with decide equality *)
decide equality.
Qed.


(* (* Successor function for BN numbers  *)
Fixpoint sucBN (b:BN) : BN :=
  match b with
      Z => U Z
    | U x => D x (*S(U x) = S(2x + 1) = 2x + 2 = D x*)
    | D x => U (sucBN x) (*S(D x)= S(2x + 2) = S(S(2x + 1)) = S(2x + 1) + 1  *)
                 (* 2(S(x)) + 1 = 2(x+1) + 1 = (2x + 2) + 1 = S(2x + 1) + 1*)  
  end.
 *)
Lemma ZnotSucBN: forall (a:BN), Z <> sucBN a.
Proof.
intros.
induction a.
simpl.
discriminate.
simpl.
discriminate.
simpl.
discriminate.
Qed.

Lemma SucBNisUorD: forall (a:BN),exists b:BN, 
  sucBN a = U b \/ sucBN a = D b.
Proof.  
  induction a.
  - simpl. exists Z. left. reflexivity.
  - simpl. exists a. right. reflexivity.
  - destruct IHa. destruct H.
  -- simpl. exists (sucBN a). left. reflexivity.
  -- simpl. exists (sucBN a). left. reflexivity.
Qed.



Lemma notSucBN : forall (a:BN), a <> sucBN a.
Proof.
intros.
destruct a.
simpl; discriminate.
simpl; discriminate.
simpl; discriminate.
Qed.


Lemma bnNonZ: forall (b:BN), b <> Z -> exists (c:BN), b = U c \/ b = D c.
Proof.
intros.
destruct b.
intuition.
exists b;left;trivial.
exists b;right;trivial.
Qed.


(* Predeccesor function with error *)

Parameter (undefBN: BN). (* we assume a constant undefBN:BN representing an undefined BN number *)

Fixpoint predBN (b:BN): BN :=
 match b with
  Z => undefBN
 |U Z => Z
 |U x => D (predBN x)
 |D x => U x
 end.


Lemma predBNUD: forall (a:BN), a <> Z -> predBN (U a) = D (predBN a).
Proof.
intros.
destruct a.
contradict H.
trivial.
reflexivity.
reflexivity.
Qed.

Lemma U_not: forall (i j :BN), U i <> U j -> i <> j.
Proof.
intros.
contradict H.
apply f_equal.
trivial.
Qed.

Lemma D_not: forall (i j :BN), D i <> D j -> i <> j.
Proof.
intros.
contradict H.
apply f_equal.
trivial.
Qed.

Lemma predsucBNinv: forall (a:BN), predBN (sucBN a) = a.
Proof.
  induction a.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - pose proof SucBNisUorD as H.
    simpl.
    specialize H with (a:= a).
    destruct H.
    destruct H.
    -- rewrite H. rewrite <-H.
       rewrite IHa. reflexivity.
    -- rewrite H. rewrite <- H.
       rewrite IHa. reflexivity.
Qed.

Lemma sucpredBNinv: forall (a:BN), a <> Z -> sucBN (predBN a) = a.
Proof.
  (* apply bnNonZ in H as H1. *)
  induction a.
  - intro. contradict H. reflexivity.
  - destruct a.
  -- simpl. intro. reflexivity.
  -- assert (U a <> Z) as H.
     apply not_eq_sym.
     apply ZnotU.
     intro.
     apply IHa in H as H1.
     assert (predBN (U (U a))= D (predBN (U a))) as H2.
     simpl. reflexivity.
     rewrite H2.
     assert (sucBN (D (predBN (U a)))= U (sucBN (predBN (U a)))). simpl. reflexivity.
     rewrite H3.
     rewrite H1.
     reflexivity.
   -- simpl. reflexivity.
   - simpl. reflexivity.
Qed.


(* Conversion functions *)

(* (* Recursive function that converts a number of type BN
 to its respective natural number*)
Fixpoint toN (b:BN) : nat :=
  match b with 
      Z => 0
    | U x => 2*(toN x) + 1
    | D x => 2*(toN x) + 2
  end.


(* Converts a nat value to BN value. 
   Inverse of the above one.*)
Fixpoint toBN (n: nat) : BN :=
  match n with
      0 => Z
    | S x => sucBN (toBN x)
  end.

Eval compute in (toN (predBN (toBN 47))).

Eval compute in toN(D(U(U Z))).

Eval compute in toN(sucBN(D(U(U Z)))).

Eval compute in toBN 16. *)

Lemma toN_sucBN : forall (b : BN), toN(sucBN b) = S(toN b).
Proof.
induction b.
simpl.
trivial.

simpl.
ring.

simpl.
rewrite IHb.
ring.
Qed.

Lemma sucBN_toBN : forall (n : nat), sucBN (toBN n) = toBN (S n).
Proof.
destruct n.
simpl.
trivial.
simpl.
trivial.
Qed.

Lemma inverse_op : forall (n : nat), toN(toBN n) = n.
Proof.
induction n.
simpl.
trivial.
simpl.
rewrite toN_sucBN.
rewrite IHn.
trivial.
Qed.


Lemma SucBNinj: forall (a b : BN), sucBN a = sucBN b -> a = b.
Proof.
intros.
assert (predBN (sucBN a)= predBN (sucBN b)).
rewrite H. reflexivity.
pose proof predsucBNinv.
specialize H1 with (a:= a) as H2.
specialize H1 with (a:= b) as H3.
rewrite <-H2.
rewrite <-H3. 
assumption.
Qed.


(* (* Definition of sum of BN elements*)

Fixpoint plusBN (a b : BN) : BN :=
  match a,b with
    | Z, b => b
    | a, Z  => a
    | U x, U y => D(plusBN x y)
    | D x, U y => U(sucBN (plusBN x y))
    | U x, D y => U(sucBN (plusBN x y))
    | D x, D y => D(sucBN (plusBN x y))                
  end.

Notation "a ⊞ b" := (plusBN a b) (at level 60). 
 *)
Lemma plusBN_toN : forall (a b : BN), toN(a ⊞ b) = toN a + toN b.
Proof.
intro.
induction a.
simpl.
trivial.
intros.
destruct b.
simpl.
ring.
simpl.
rewrite IHa.
ring.
simpl.
rewrite toN_sucBN.
rewrite IHa.
ring.
destruct b.
simpl.
ring.
simpl.
rewrite toN_sucBN.
rewrite IHa.
ring.
simpl.
rewrite toN_sucBN.
rewrite IHa.
ring.
Qed.



Lemma plus_neutro: forall (b:BN), b ⊞ Z = b.
Proof.
intros.
destruct b.
simpl;trivial.
simpl;trivial.
simpl;trivial.
Qed.
Lemma plus_sucBN_ZU: forall (b : BN),  sucBN (b) = b ⊞ U Z.
Proof.
  intros.
  induction b.
  - simpl. reflexivity.
  - simpl. rewrite plus_neutro. reflexivity.
  - simpl. rewrite plus_neutro. reflexivity.
Qed.
Lemma plus_sucBN_ZUU: forall (b : BN),  sucBN(sucBN (b)) = b ⊞ D Z.
Proof.
intros.
induction b.
- simpl. reflexivity.
- simpl. rewrite plus_neutro.
  reflexivity.
- simpl. rewrite plus_neutro.
  reflexivity.
Qed.

Lemma plus_U: forall (b : BN),  sucBN (b ⊞ b) = U b.
Proof.
intros.
induction b.
simpl.
trivial.
simpl.
rewrite IHb.
trivial.
simpl.
rewrite IHb.
simpl.
trivial.
Qed.



Lemma plus_D: forall (b : BN),  sucBN (sucBN b ⊞ b) = D b.
Proof.
intros.
induction b.
simpl.
trivial.
simpl.
rewrite plus_U.
trivial.
simpl.
rewrite IHb.
trivial.
Qed.


Lemma plusSuc : forall (b c: BN), sucBN (b ⊞ c) = sucBN b ⊞ c.
Proof.
  induction b.
  - induction c.
    -- simpl. reflexivity.
    -- simpl. reflexivity.
    -- simpl. reflexivity. 
  - induction c.
    -- simpl. reflexivity.
    -- simpl. reflexivity.
    -- simpl. reflexivity. 
  - induction c.
    -- simpl. reflexivity.
    -- simpl.
        specialize IHb with (c:=c).
        rewrite IHb.
        reflexivity.
    -- simpl.
       specialize IHb with (c:= c) as H1.
       rewrite H1.
       reflexivity.
Qed.

Lemma plus_toBN:  forall (n m: nat), toBN(n + m) = toBN n ⊞ toBN m.
Proof.
intros.
induction n.
simpl.
trivial.
simpl.
rewrite IHn.
rewrite <- plusSuc.
trivial.
Qed.

Lemma inverse_op_2 : forall (b:BN), toBN(toN b) = b.
Proof.
intros.
induction b.
- simpl. reflexivity.
- simpl.
  rewrite plus_toBN.
  rewrite plus_toBN.
  rewrite plus_toBN.
  simpl.
  rewrite IHb.
  rewrite plus_neutro.
  rewrite <-plus_sucBN_ZU with (b ⊞ b).
  rewrite plus_U. 
  reflexivity.
- simpl.  
  rewrite Nat.add_0_r.
  rewrite plus_toBN.
  rewrite plus_toBN.
  rewrite IHb.
  simpl.
  pose proof plus_D (b) .
  rewrite <-H.
  rewrite <-plusSuc.
  rewrite plus_sucBN_ZUU.
  reflexivity.
Qed.


Lemma plusComm: forall (a b:BN), (a ⊞ b) = (b ⊞ a).
Proof.
intro.
induction a.
- intro. simpl. rewrite plus_neutro. reflexivity.
- intro.
  induction b.
  reflexivity.
  simpl. rewrite IHa. reflexivity.
  simpl. rewrite IHa. reflexivity.
- intro. induction b.
  simpl.  reflexivity.
  simpl. rewrite IHa. reflexivity.
  simpl. rewrite IHa. reflexivity.
Qed.


Lemma plusSuc_2 : forall (b c: BN), sucBN (b ⊞ c) = b ⊞ sucBN c.
Proof.
intros.
rewrite plusComm.
rewrite plusSuc.
rewrite plusComm.
reflexivity.
Qed.


Lemma plusBN_Z_Z: forall (x y:BN), x ⊞ y = Z -> x = Z /\ y = Z.
Proof.
intros.
split.
induction x.
reflexivity.
  - symmetry in H.
  contradict H.
  destruct y.
  simpl.
  apply ZnotU.
  simpl. apply ZnotD with (a:= (x ⊞ y)).
  simpl. apply ZnotU with (a:= sucBN (x ⊞ y))  .
- symmetry in H.
  contradict H.
  destruct y.
  simpl.
  apply ZnotD.
  simpl. apply ZnotU with (a:= sucBN (x ⊞ y)).
  simpl. apply ZnotD with (a:=sucBN(x ⊞ y) )  .
- induction y.
  reflexivity.
  symmetry in H.
  contradict H.
  destruct x.
  simpl.
  apply ZnotU.
  simpl. apply ZnotD with (a:= (x ⊞ y)).
  simpl. apply ZnotU with (a:= sucBN (x ⊞ y))  .
  symmetry in H.
  contradict H.
  destruct x.
  simpl.
  apply ZnotD.
  simpl. apply ZnotU with (a:= sucBN (x ⊞ y)).
  simpl. apply ZnotD with (a:=sucBN(x ⊞ y) )  .
Qed.



Lemma UDCase: forall (x:BN), x <> Z -> exists (b:BN), x = U b \/ x = D b.
Proof.
intros.
destruct x.
intuition.
exists x;left;trivial.
exists x;right;trivial.
Qed.

Lemma suc_not_zero: forall (x:BN), sucBN x <> Z.
Proof.
intros.
destruct x.
simpl;discriminate.
simpl;discriminate.
simpl;discriminate.
Qed.

Lemma addition_a_a : forall (a b:BN), a ⊞ a = b ⊞ b -> a = b.
Proof.
intros.
apply (f_equal sucBN) in H.
rewrite plus_U in H.
rewrite plus_U in H.
apply UInj.
trivial.
Qed.

Lemma addition_SucBNa_a : forall (a b:BN), sucBN a ⊞ a = sucBN b ⊞ b -> a = b.
Proof.
intros.
rewrite <- plusSuc in H.
rewrite <- plusSuc in H.
apply SucBNinj in H.
apply (f_equal sucBN) in H.
rewrite plus_U in H.
rewrite plus_U in H.
apply UInj.
trivial.
Qed.

(** orderbn*)


(* Inductive ltBN : BN -> BN -> Prop :=
 | ltBNZU : forall (a:BN), ltBN Z (U a)
 | ltBNZD : forall (a:BN), ltBN Z (D a)
 | ltBNUU : forall (a b:BN), ltBN a b -> ltBN (U a) (U b)
 | ltBNUDeq : forall (a :BN), ltBN (U a) (D a) 
 | ltBNUD : forall (a b:BN), ltBN a b -> ltBN (U a) (D b) 
 | ltBNDU : forall (a b:BN), ltBN a b -> ltBN (D a) (U b)
 | ltBNDD : forall (a b:BN), ltBN a b -> ltBN (D a) (D b).


Inductive lteqBN: BN -> BN -> Prop :=
 | lteqBNref: forall (a:BN), lteqBN a a
 | lteqBNl: forall (a b: BN), ltBN a b -> lteqBN a b.


Notation "a <BN b" := (ltBN a b) (at level 70).
Notation "a <BN b <BN c" := (ltBN a b /\ ltBN b c) (at level 70, b at next level).

Notation "a ≤BN b" := (lteqBN a b) (at level 70).
 *)
Lemma lt_U: forall (a b:BN), a <BN b <-> (U a) <BN U b.
Proof.
intros.
split.
+ intro. 
  apply ltBNUU. 
  assumption.
+ intro.
  inversion H.
  assumption.
Qed.


Lemma lt_D: forall (a b:BN), a <BN b <-> (D a) <BN D b.
Proof.
intros. split.
+ intros. apply ltBNDD.
  assumption.
+ intros.
  inversion H.
  assumption.
Qed.

Lemma ltBN_arefl: forall (a:BN), ~ a <BN a.
Proof.
intros.
induction a.
unfold not.
intros.
inversion H.
contradict IHa.
inversion IHa.
trivial.
contradict IHa.
inversion IHa.
trivial.
Qed.

Create HintDb PNatDb.

Hint Resolve ltBN_arefl: PNatDb.

Lemma ltBN_asym: forall (a b:BN), a <BN b -> ~ b <BN a.
Proof.
intros.
induction H.
unfold not;intros.
inversion H.
unfold not;intros.
inversion H.
contradict IHltBN.
inversion IHltBN.
trivial.
unfold not;intros.
inversion H.
apply (ltBN_arefl a).
trivial.
(*exact (ltBN_arefl a H2).*)
unfold not;intros.
inversion H0.
intuition.
contradict IHltBN.
inversion IHltBN.
rewrite H2 in H.
trivial.
trivial.
contradict IHltBN.
inversion IHltBN.
trivial.
Qed.

Hint Resolve ltBN_asym: PNatDb.

(*Lemma ltBN_antisym: forall (a b:BN), ltBN a b -> ltBN b a -> *)

Lemma ltBN_tr: forall (b c:BN), b <BN c -> forall (a:BN), a <BN b -> a <BN c.
Proof.
intro.
intro.
intro.
induction H.
- intros. inversion H.
- intros. inversion H.
- intros. 
Admitted.

Hint Resolve ltBN_tr: PNatDb.


Lemma ltBN_trans: forall (a b c:BN), a <BN b -> b <BN c -> a <BN c.
Proof.
intros.
eapply ltBN_tr.
eexact H0.
trivial.
Qed.

Hint Resolve ltBN_trans: PNatDb.

Lemma lt_lteqBN_trans: forall (a b c:BN), a <BN b -> b ≤BN c -> a <BN c.
Proof.
intros.
inversion H0.
rewrite H2 in H.
trivial.
eapply ltBN_trans.
eexact H.
trivial.
Qed.

Hint Resolve lt_lteqBN_trans: PNatDb.

Lemma lteqBN_trans: forall (a b c:BN), a ≤BN b -> b ≤BN c -> a ≤BN c.
Proof.
intros.
inversion H.
trivial.
inversion H0.
rewrite H5 in H.
trivial.
constructor.
eapply ltBN_trans.
eexact H1.
trivial.
Qed.

Hint Resolve lteqBN_trans: PNatDb.

Lemma ltDs: forall (a:BN), (D a) <BN (U (sucBN a)).
Proof.
intros.
induction a.
simpl.
constructor.
constructor.
simpl.
constructor.
constructor.
simpl.
constructor.
trivial.
Qed.

Hint Resolve ltDs: PNatDb.
Lemma ltBN_aUZ: forall (a:BN), a <BN U Z -> a =Z.
Proof.
intros.
induction a.
reflexivity.
inversion H.
inversion H2.
inversion H.
inversion H2.
Qed.


Lemma lteqBN_Za: forall (a:BN), Z ≤BN a.
Proof.
intros.
destruct a.
- constructor.
- constructor.
  apply ltBNZU.
- constructor.
  apply ltBNZD.
Qed.

Lemma lts: forall (a:BN), a <BN (sucBN a).
Proof.
intros.
induction a.
constructor.
simpl.
constructor.
simpl.
constructor.
trivial.
Qed.

Hint Resolve lts: PNatDb.

Lemma lteqs: forall (a:BN), a ≤BN (sucBN a).
Proof.
intros.
induction a.
constructor.
constructor.
simpl.
constructor.
constructor.
simpl.
constructor.
constructor.
inversion IHa.
contradict H0.
apply notSucBN.
trivial.
Qed.

Hint Resolve lteqs: PNatDb.

Lemma ltpred : forall (a:BN), a <> Z -> (predBN a) <BN a.
Proof.
intros.
induction a.
- contradict H. reflexivity.
- simpl. destruct a. 
  + constructor. 
  + apply ltBNDU. 
    apply IHa. 
    apply not_eq_sym.
    apply ZnotU.
  + apply ltBNDU.
    apply IHa.
    apply not_eq_sym.
    apply ZnotD. 
- simpl. apply ltBNUDeq.
Qed.



Hint Resolve ltpred: PNatDb.

Lemma lt1: forall (b a:BN), a <BN (sucBN b) -> a ≤BN b.
Proof.
intro.
induction b.
- intros.
  inversion H.
  constructor.
  inversion H2.
  inversion H2.
- intros. 
  inversion H.
  * apply lteqBN_Za.
  * constructor.
  * constructor.
    constructor.
    assumption.
  * constructor.
    constructor.
    assumption.
- intros.
  inversion H.
  apply lteqBN_Za.
  inversion H2.
  -- constructor.
     constructor.
(*      
     constructor.
  apply IHb.
  constructor.
  constructor.

intros.
induction a.
apply lteqBN_Za.
 
inversion H.
apply lteqBN_Za.
apply lteqBN_Za.
- admit.
-  *)

(* intro.
induction b.
- intros.
  apply ltBN_aUZ in H.
  rewrite H. constructor.
- intros.
   admit.
- intros. admit.
- intros.
apply lteqBN_Z.

induction H.
- apply lteqBN_Z.
- apply lteqBN_Z.
- inversion IHltBN. *)
Admitted.

Hint Resolve lt1: PNatDb.

Lemma lt2: forall (b a:BN), a ≤BN b -> a <BN (sucBN b).
Proof.
intro.
induction b.
- intros.
  inversion H.
  subst.
  constructor.
  subst.
  inversion H0.
- intros.
  inversion H.
  subst.
  constructor.
  subst.
  induction a.
  constructor.
  inversion H0.
  subst.
  simpl.
  constructor.
  assumption.
  simpl.
  constructor.
  inversion H0.
  assumption.
- intros.
  inversion H.
  apply lts.
  subst.
  inversion H0.
  constructor.
  simpl.
  constructor.
  apply lts.
  simpl.
  subst.
  constructor.
  apply IHb.
  constructor.
  assumption.
  simpl.
  constructor.
  apply IHb.
  constructor.
  assumption.
Qed.


Hint Resolve lt2: PNatDb.

Lemma lteqBN_suc_pred : forall (a b:BN), a <> Z -> a ≤BN (sucBN b) -> (predBN a) ≤BN b.
Proof.
intros.
assert ((predBN a) <BN a).
apply ltpred.
trivial.
assert (predBN a <BN sucBN b).
eapply lt_lteqBN_trans.
eexact H1.
trivial.
apply lt1.
trivial.
Qed.

Hint Resolve lteqBN_suc_pred: PNatDb.


Lemma ltaux1: forall (j:BN), Z ≤BN (D j) -> Z ≤BN j.
Proof.
intros.
apply lteqBN_Za.
Qed.


Lemma lteqBN_refl : forall (b:BN), b ≤BN b.
Proof.
intros.
constructor.
Qed.

Lemma lteqBN_Z : forall (b:BN), Z ≤BN b.
Proof.
intros.
destruct b.
constructor.
constructor;constructor.
constructor;constructor.
Qed.

Theorem not_lt_suc: forall (a:BN), ~ exists (b:BN), a <BN b /\ b <BN (sucBN a).
Proof.
intros.
intro.
induction a.
+ destruct H.
  destruct H.
  - apply ltBN_aUZ in H0.
  rewrite H0 in H.
  inversion H.
+ apply IHa.
  destruct H.
  destruct H.
  destruct x.
  inversion H.
  - simpl in H0. 
(*     apply 
destruct H.
destruct H.
induction a.
- apply ltBN_aUZ in H0.
  rewrite H0 in H.
  inversion H.
- simpl in H0.
  destruct x.
  + inversion H.
  + 
  simpl in IHa. *)
Admitted.


Lemma trichotomy: forall (a b:BN), a <BN b \/ a=b \/ b <BN a.
Proof.
Admitted.

Lemma not_lt: forall (a b:BN), b ≤BN a -> ~ a <BN b.
Proof.
Admitted.

Lemma sucBN_lt: forall (a b:BN), sucBN a <> b -> a <BN b -> (sucBN a) <BN b.
Proof.
Admitted.

(* Next lemmas are used for Okasaki's size *)

Lemma lteqBN_U_U:forall (a b:BN), (U a) ≤BN (U b) -> a ≤BN b.
Proof.
intros.
inversion H.
constructor.
inversion H0.
constructor.
trivial.
Qed.

Lemma lteqBN_D_D : forall (a b : BN), (D a) ≤BN (D b)-> a ≤BN b.
Proof.
intros.
inversion H.
constructor.
inversion H0.
constructor.
trivial.
Qed.

Lemma lteqBN_U_D:forall (a b:BN), (U a) ≤BN (D b) -> a ≤BN b.
Proof.
intros.
inversion H.
inversion H0.
constructor.
constructor.
trivial.
Qed.

Lemma lteqBN_D_U:forall (a b:BN), (D a) ≤BN (U b) -> a ≤BN b.
Proof.
intros.
inversion H.
inversion H0.
constructor.
trivial.
Qed.
Lemma lt_suc_lteq: forall (a b:BN), a <BN b <-> (sucBN a) ≤BN b.
Proof.
intros.
split. 
+ intro. induction H.
- simpl. destruct a.
  -- constructor.
  -- simpl. constructor. 
     apply ltBNUU.
     constructor.
  -- constructor.
     apply ltBNUU.
     constructor. 
- destruct a.
  -- constructor.
     constructor.
  -- constructor.
     constructor.
     constructor.
  -- constructor.
     constructor.
     constructor.
- simpl.
  constructor.
  constructor.
  assumption.
- constructor.
- simpl.
  constructor.
  constructor.
  assumption.
- simpl.
  admit. (* probar monotonia de U*)
- simpl. 
  admit. (* probar monotonía  de D*)
+ intro.
(*   constructor.
  constructor.
  assumption.
- inversion H.
-   *)
(* intro. *)
pose proof (lts a).
eapply lt_lteqBN_trans.
apply H0.
assumption.
Admitted.

Lemma lteqBN_suc: forall (a b:BN), a ≤BN b -> (sucBN a) ≤BN (sucBN b). 
Proof.
intros.
inversion H.
constructor.
apply lt_suc_lteq.
apply lt2.
trivial.
Qed.



Lemma bbalCond_eqs: forall (s t:BN), t ≤BN s -> s ≤BN sucBN t -> s = t \/ s = sucBN t.  (* nov-2016, C.V. *)
Proof.
intros.
inversion H.
intuition.
inversion H0.
intuition.
exfalso.
eapply not_lt_suc.
exists s.
split.
exact H1.
assumption.
Qed.








