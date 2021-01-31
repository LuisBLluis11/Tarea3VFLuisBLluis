(* From Tarea3VF Require Import Defs_BT .
From Tarea3VF Require Import Props_BN . *)

Add LoadPath "C:\Users\spide\Documents\Tareas\VerificacionFormal\Tareas\Tarea3\Tarea3VFLuisBLluis" as camino. 

Load Props_BN .


(** 2.- binary_tree *)
(* (* Definition of binary trees and some of their properties  *)

Parameter (A:Type)
          (eq_dec_A: forall (x y:A),{x=y}+{x<>y})
          (undefA : A).
          

(* Binary trees defined here*)
Inductive BTree : Type :=
    E : BTree   
  | N : A -> BTree  -> BTree  -> BTree.

Check BTree_ind.

 *)
(* Parameter (undefBTree : BTree). *)
(* Parameter (A:Type). *)
(* Parameter (eq_dec_A: forall (x y:A),{x=y}+{x<>y}). *)
(* Parameter (undefA : A).
Parameter (undefBN: BN). *)
(* Parameter (allBal: forall (t:BTree), bbal t). *)


Theorem eq_btree_dec: forall (s t:BTree), {s=t} + {s<>t}.
Proof.
intros.
decide equality.
apply eq_dec_A.
Qed. 


Lemma nonE_tree: forall (t:BTree), t <> E -> exists (a:A) (t1 t2:BTree), t = N a t1 t2.
Proof.
intros.
destruct t.
intuition.
exists a.
exists t1.
exists t2.
trivial.
Qed.

(** 4.- braunT_bn*)
(*
(* *size on binary trees defined next*)
Fixpoint bsize (t:BTree): BN :=
 match t with
  E => Z
 |N x s t =>  sucBN ((bsize s) ⊞ (bsize t))
 end.

Check bsize. *)

Lemma bsize_Z: 
    forall (t:BTree), bsize t = Z <-> t = E.
Proof.
intros t0.
split.
intros.
destruct t0.
intuition.
intros.
simpl in H.
symmetry in H.
contradict H.
apply ZnotSucBN.
intros.
rewrite H.
simpl.
reflexivity.
Qed.

Lemma bsize_nonZ: 
  forall (t:BTree), t <> E <-> bsize t <> Z.
Proof.
intros.
split.
intro.
contradict H.
apply bsize_Z.
trivial.
intro.
intro.
contradict H.
rewrite H0.
simpl.
reflexivity.
Qed.


Lemma btNonE: 
  forall (t:BTree) (b:BN), t <> E -> 
          exists (b:BN), 
          bsize t = U b \/ bsize t = D b.
Proof.
intros.
apply bsize_nonZ in H.
apply (bnNonZ (bsize t)) in H.
trivial.
Qed.

(*
(* * Balance condition on Braun trees *)
Inductive bbal : BTree -> Prop:= 
 |bbalE : bbal E 
 |bbalN : forall (a: A) (s t: BTree), 
        bbal s -> bbal t -> 
        (bsize t) ≤BN (bsize s) -> 
        (bsize s) ≤BN (sucBN (bsize t)) -> 
                                      bbal (N a s t).

Check bbal_ind.
*)
 (*Parameter (allBal: forall (t:BTree), bbal t). *)



Lemma prop_0_U : 
  forall (a:A) (s t:BTree) (b:BN), 
        bbal (N a s t) -> bsize(N a s t) = U b -> 
          bsize s = b /\ bsize t = b.
Proof.
intros.
simpl in H0.
assert (H0b:=H0).
rewrite <- plus_U in H0.
apply SucBNinj in H0.
inversion H.
destruct(bbalCond_eqs (bsize s) (bsize t)).
trivial.
trivial.
rewrite <- H8 in H0.
apply addition_a_a in H0.
rewrite <- H8.
intuition.
rewrite H8 in H0b.
rewrite plus_D in H0b.
inversion H0b.
Qed.


Lemma prop_0_D : 
  forall (a:A) (s t:BTree) (b:BN), 
        bbal (N a s t) ->
           bsize(N a s t) = D b -> 
              bsize s = sucBN b /\ bsize t = b.
Proof.
intros.
simpl in H0.
assert (H0b:=H0).
rewrite <- plus_D in H0.
apply SucBNinj in H0.
inversion H.
destruct(bbalCond_eqs (bsize s) (bsize t)).
trivial.
trivial.
rewrite <- H8 in H0b.
rewrite plus_U in H0b.
inversion H0b.
rewrite H8 in H0.
apply addition_SucBNa_a in H0.
rewrite <- H0.
intuition.
Qed.

Corollary size_caseU: 
  forall (a:A) (l r:BTree) (b:BN), 
        bsize (N a l r) = U b -> bsize l = bsize r.
Proof.
intros.
assert (HBal := allBal (N a l r)).
apply (prop_0_U a l r b) in H.
intuition.
rewrite <- H1 in H0.
intuition. intuition.
Qed.

Corollary size_caseD: forall (a:A) (l r:BTree) (b:BN), 
                        bsize (N a l r) = D b 
                           -> bsize l = sucBN (bsize r).
Proof.
intros.
assert (HBal := allBal (N a l r)).
apply (prop_0_D a l r b) in H.
intuition.
rewrite <- H1 in H0.
intuition. intuition.
Qed.

Corollary bbal_size_r: forall (a:A) (l r:BTree), 
                          bsize (N a l r) = U (bsize r) \/ 
                          bsize (N a l r) = D (bsize r).
Proof.
intros.
assert (HBal:=allBal (N a l r)).
destruct (bnNonZ (bsize (N a l r))).
simpl.
assert (Z <> sucBN (bsize l ⊞ bsize r)).
apply ZnotSucBN.
intuition.
destruct H.
apply prop_0_U in H.
simpl.
destruct H.
rewrite H.
rewrite H0.
rewrite plus_U.
intuition.
trivial.
apply prop_0_D in H.
destruct H.
simpl.
rewrite H.
rewrite H0.
rewrite plus_D.
intuition.
trivial.
Qed.

Theorem bbal_size_r2: forall (a:A) (l r:BTree), 
    (bsize (N a l r)) ≤BN (D (bsize r)). 
Proof.
intros a l r.
destruct (bbal_size_r a l r).
constructor.
rewrite H.
constructor.
rewrite H.
constructor.
Qed.

Theorem bbal_size_l: forall (a:A) (l r:BTree), 
    (bsize (N a l r)) ≤BN (U (bsize l)). 
Proof.
intros.
assert (HBal:=allBal (N a l r)).
destruct (bnNonZ (bsize (N a l r))).
- simpl.
  assert (Z <> sucBN (bsize l ⊞ bsize r)).
  apply ZnotSucBN.
  intuition.
- destruct H.
  + apply prop_0_U in H.
    * simpl.
      destruct H.
      subst.
      rewrite H0. 
      rewrite plus_U.
      constructor.
    * assumption.
  +  apply prop_0_D in H.
    * simpl.
      destruct H.
rewrite H.
rewrite H0.
rewrite plus_D.
constructor.
constructor.
apply lts.
* trivial.
Qed.

(* ============================================= *)
          

Lemma lt_U_bsize: forall (b:BN) (a:A) (t1 t2:BTree), 
  (U b) <BN (bsize (N a t1 t2)) -> b <BN (bsize t1).
Proof.
intros b a t1 t2 H.
assert ((bsize (N a t1 t2)) ≤BN (U (bsize t1))).
apply bbal_size_l.
assert ((U b) <BN (U (bsize t1))).
eapply lt_lteqBN_trans.
eexact H.
trivial.
inversion H1.
trivial.
Qed.



Theorem rightE: forall (a:A) (t1 t2:BTree), bbal(N a t1 t2) -> t2 = E -> (t1 = E \/ exists (aa:A), t1 = (N aa E E)).
Proof.
intros.
inversion H.
destruct (bbalCond_eqs (bsize t1) (bsize t2)).
trivial.
trivial.
rewrite H0 in H8.
simpl in H8.
apply bsize_Z in H8.
intuition.
rewrite H0 in H8.
right.
destruct t1.
simpl in H8.
inversion H8.
simpl in H8.
replace (U Z) with (sucBN Z) in H8.
apply SucBNinj in H8.
apply plusBN_Z_Z in H8.
destruct H8.
apply bsize_Z in H8.
apply bsize_Z in H9.
exists a1.
rewrite H8.
rewrite H9.
trivial.
intuition.
Qed.


Lemma lt_D_bsize: forall (b:BN) (a:A) (t1 t2:BTree), (D b) <BN (bsize (N a t1 t2)) -> b <BN (bsize t2).
Proof.
intros b a t1 t2 H.
assert ((bsize (N a t1 t2)) ≤BN (D (bsize t2))).
apply bbal_size_r2.
assert ((D b) <BN (D (bsize t2))).
eapply lt_lteqBN_trans.
eexact H.
trivial.
inversion H1.
trivial.
Qed.



Lemma bbal_leaf: forall (a:A), bbal (N a E E).
Proof.
intro a.
constructor.
constructor.
constructor.
apply lteqBN_refl. 
apply lteqs.
Qed.



Theorem leftE_leaf: forall (t1 t2:BTree) (a:A), bbal (N a t1 t2) -> t1 = E -> t2 = E.
Proof.
intros t1 t2 c HBal H.
inversion HBal.
rewrite H in H5.
simpl in H5.
inversion H5.
apply bsize_Z in H9.
trivial.
inversion H7.
Qed.



Lemma bbal_inv: forall (t:BTree), t <> E ->  
       (exists (z:A), t = N z E E)  \/ 
        exists (z:A) (r1 r2:BTree), 
               bbal r1 /\ 
               bbal r2 /\ 
               r1 <> E /\ 
               t = N z r1 r2.
Proof.
 intros.
 pose proof allBal (t) as H0.
 induction t.
 contradict H. reflexivity.
 
(*  inversion H0.
 induction t.
 contradict H. reflexivity.
 inversion H1.
 destruct s.
 - left. simpl in H3.  *)


  
  
Admitted.

(** 5.- lookupdBN*)
(* 

Fixpoint lookup_bn (t:BTree) (b: BN) : A :=
 match t,b with
  |E, b => undefA
  |N x s t,Z => x 
  |N x s t, U a => lookup_bn s a   (* U a = 2a+1 *)
  |N x s t, D a => lookup_bn t a   (* D a = 2a + 2 *) 
 end.



Fixpoint update (t:BTree) (b: BN) (x : A) : BTree :=
 match t,b with
  |E, b => undefBTree
  |N y s t, Z =>  N x s t
  |N y s t, U a => N y (update s a x) t
  |N y s t, D a => N y s (update t a x)
 end.


Check bbal_inv.
 *)


Lemma lkp_upd_BN: forall (t:BTree) (x:A) (b:BN), t <> E -> 
                       b <BN (bsize t) -> 
                       lookup_bn (update t b x) b = x.
Proof.
intros t x.
assert (H:=allBal t).
(*Induction on t*)
induction t.
- (*Base case t = E *)
intuition.
- (*Induction step t = N a t1 t2*)
intros.
(*cases on BNat number b*)
destruct b.
+ (*1. b=Z*)
reflexivity.
+ (*2. b = U b*)
destruct (eq_btree_dec t1 E).
(*Cases on t1*)
* (*i) t1=E A*)
assert (t2 = E).
-- apply (leftE_leaf t1 t2 a).
   ++ eexact H.
   ++ assumption.
-- (*t1=E  and t2=E *)
   subst.
   simpl in H1.
   inversion H1.
   inversion H4.
* (*ii) t1<>E A*)
simpl. 
apply IHt1.
-- inversion H.
   assumption.
-- assumption.
-- eapply lt_U_bsize.
   exact H1.
+ (*3. b = D b*)
  destruct (eq_btree_dec t2 E).
  * destruct (rightE a t1 t2).
    -- assumption.
    -- assumption.
    -- simpl.
       subst.
       simpl in H1.
       inversion H1.
       inversion H4.
    -- destruct H2.
       subst.
       simpl in H1.
       inversion H1.
       inversion H4.
* simpl. 
  apply IHt2.
  -- inversion H.
     assumption.
  -- assumption.
  -- eapply lt_D_bsize.
     exact H1.
Qed.




Lemma lkp_upd_BNindbal: forall (t:BTree) (x:A) (b:BN), t <> E -> 
                       b <BN (bsize t) -> 
                       lookup_bn (update t b x) b = x.
Proof.
intros t x.
assert (H:=allBal t).
induction H.
- intuition.
- intros.
  destruct b.
  + reflexivity.
  + simpl.
    destruct (eq_btree_dec s E).
    * destruct (eq_btree_dec t E).
      -- subst.
         simpl in H4.
         apply lt_U in H4.
         inversion H4.
      -- subst.
         simpl in H1.
         inversion H1. 
         ++ subst.
            apply bsize_nonZ in n.
            contradiction n.  
         ++ inversion H5.
    * apply IHbbal1.
      -- assumption.
      -- apply lt_U.
         eapply lt_lteqBN_trans.
         ++ exact H4.
         ++ apply bbal_size_l.
  + destruct (eq_btree_dec t E).
    * destruct (eq_btree_dec s E). 
       -- subst.
          simpl in H4.
          inversion H4.
          inversion H7.
       -- subst.
          simpl in H2.
          inversion H2.
          ++ simpl in H4.
             rewrite H7 in H4.
             simpl in H4. 
             inversion H4.
             inversion H9.
          ++ subst.
             inversion H5.
             ** contradict n.
             apply bsize_Z.
             intuition. 
             ** inversion H8.
             ** inversion H8.
    *  simpl.
       apply IHbbal2.
       -- assumption.
       -- apply lt_D.
          eapply lt_lteqBN_trans.
          ++ exact H4.
          ++ apply bbal_size_r2.  
Qed.       
       
          
Lemma elmnt_lkp_upd : forall (t:BTree) (i j:BN), 
                        i <BN (bsize t) -> j <BN (bsize t) -> 
                        i <> j -> 
                        forall (x:A), 
                          lookup_bn (update t i x) j = lookup_bn t j.
Proof.
intros t.
induction t.
(* t = E*)
- intros.
simpl in H0.
inversion H0.
- (* t = N a t1 t2 *)
intros.
assert (tBal:=allBal (N a t1 t2)).
destruct (bbal_inv (N a t1 t2)).
+ discriminate.
+ (* exists z : A, N a t1 t2 = N z E E *)
destruct H2.
inversion H2.
subst.
simpl in H.
inversion H.
* subst.
  simpl in H0.
  inversion H0.
  -- subst. intuition.
  -- reflexivity.
  -- reflexivity. 
* destruct j.
  -- reflexivity.
  -- inversion H5.
  -- inversion H5.
* inversion H5.
+ (*  exists (z : A) (r1 r2 : BTree),
         bbal r1 /\ bbal r2 /\ r1 <> E /\ N a t1 t2 = N z r1 r2 *)
do 4 (destruct H2).
destruct H3.
destruct H4.
destruct H5.
destruct i.
* destruct j. 
  -- intuition.
  -- reflexivity.
  -- reflexivity.
* destruct j.
  -- reflexivity.
  -- simpl.
     apply IHt1. 
     ++ apply lt_U.
        eapply lt_lteqBN_trans.
        ** exact H.
        ** apply bbal_size_l. 
     ++ apply lt_U.
        eapply lt_lteqBN_trans.
        ** exact H0.
        ** apply bbal_size_l.
     ++ contradict H1.
        subst;reflexivity.
   -- reflexivity.
  * destruct j.
    -- reflexivity.
    -- reflexivity.
    -- simpl. 
       apply IHt2. 
     ++ apply lt_D.
        eapply lt_lteqBN_trans.
        ** exact H.
        ** apply bbal_size_r2.
     ++ apply lt_D.
        eapply lt_lteqBN_trans.
        ** exact H0.
        ** apply bbal_size_r2.
     ++ contradict H1.
        subst;reflexivity.
Qed.


Lemma bsize_upd: forall (t:BTree) (x:A) (b:BN), 
                  b <BN bsize t -> bsize t = bsize (update t b x).
Proof.
intro t.
induction t.
- (* Base case *)
intuition.
inversion H.
- (* Inductive step *)
intros.
destruct (bbal_inv (N a t1 t2)).
+ discriminate.
+ destruct H0.
  rewrite H0 in H.
  simpl in H.
  inversion H.
  * (* b = Z *)
   reflexivity.
  * (* U a0 = b, a < Z *)
    inversion H3.
  * (* D a0 = b, a < Z *)
    inversion H3.
+ do 4 (destruct H0).
  destruct H1.
  destruct H2.
  inversion H3.
  subst.
  destruct b.
  * (* Z *)
    reflexivity.
  * (* U b*)
   simpl.
   rewrite (IHt1 x b).
   -- reflexivity.
   -- apply (lt_U_bsize b x0 x1 x2).
      assumption. 
  * (* b = D b *)
    simpl.
    rewrite (IHt2 x b).
    -- reflexivity.
    -- apply (lt_D_bsize b x0 x1 x2).
       assumption.
Qed.
     
(** 6.-btExtensions *)

Lemma le_hasroot: forall (a:A)(t:BTree), 
    exists (t1 t2:BTree),
    (le a t)= N a t1 t2.
Proof.    
intros.
induction t.
- exists E. exists E. simpl. reflexivity.
- simpl. exists (le a0 t2). exists t1.
  reflexivity.
Qed.

Lemma he_hasroot: forall (a:A)(t:BTree), 
    exists (y:A)(t1 t2:BTree),
    (he a t)= N y t1 t2.
Proof.
intros.
induction t.
- simpl. exists a. exists E. exists E. reflexivity.
- simpl.
  pose proof SucBNisUorD (bsize t1 ⊞ bsize t2).
  destruct H. destruct H.
  + rewrite H.
    destruct IHt1. destruct H0. 
    destruct H0.
    exists a0. exists (he a t1). exists t2.
    reflexivity.
  + rewrite H.
    exists a0. exists t1. exists (he a t2).
    reflexivity.
Qed.
  

(*
Lemma le_nonE: forall (a x:A) (t1 t2:BTree), le x (N a t1 t2) =  N x (le a t2) t1.
*)


Lemma bsize_le: forall (t:BTree) (x:A), bsize (le x t) = sucBN (bsize t).
Proof.
intro.
assert (HBal := allBal t).  
induction HBal.
- reflexivity.
- intro.
  simpl.
  rewrite IHHBal2.
  rewrite <- plusSuc.
  rewrite plusComm.
  reflexivity.
Qed.



Lemma bal_le: forall (t:BTree), bbal t -> 
                 forall (x:A), bbal (le x t).
Proof.
intros t HtBal.
induction HtBal.
- simpl.
  apply bbal_leaf.
- intros.
  simpl.
  constructor.
  + apply IHHtBal2.
  + assumption.
  + rewrite bsize_le.
    assumption.
  + rewrite bsize_le.
    apply lteqBN_suc.
    assumption.
Qed.

Lemma le_head: forall (t: BTree) (x:A),  lookup_bn (le x t) Z = x.
Proof.
intros.
destruct t.
- intuition.
- intuition.
Qed.


Lemma le_idx: forall (t:BTree),  bbal t -> 
forall (j:BN), j <BN (bsize t) -> forall (x:A), lookup_bn (le x t) (sucBN j) = lookup_bn t j.
Proof.
intros t B.
induction B.
- intros.
  simpl in H.
  inversion H.
- intros.
  clear IHB1.
  destruct j.
  + simpl.
    apply le_head.
  + reflexivity.
  + simpl.
    apply IHB2.
    apply (lt_D_bsize j a s t).
    assumption.
Qed.


(*High Extension*)

Lemma bsize_he: forall (t:BTree) (x:A), 
                    bsize (he x t) = sucBN (bsize t).
Proof.
intro.
induction t.
- intuition.
- intros.
  destruct (bbal_size_r a t1 t2).
  + simpl in H.
    simpl.     
    rewrite H.
    simpl.
    rewrite IHt1.
    rewrite <- plusSuc.
    rewrite H. 
    intuition.
  + simpl in H.
    simpl.
    rewrite H.
    simpl.
    rewrite IHt2.
    rewrite <- plusSuc_2.
    rewrite H.
    intuition.
Qed.



Lemma bal_he: forall (t:BTree), bbal t -> 
                forall (x:A), bbal (he x t).
Proof.
intros t Ht.
induction t.
- simpl.
  apply bbal_leaf.
- intros.
  inversion Ht.
  subst.
  destruct (bbal_size_r a t1 t2).
  + assert(H6:=H).
    apply size_caseU in H.
    simpl in H6.
    simpl.
    rewrite H6.
    constructor.
    * apply IHt1.
      assumption.
    * assumption.
    * rewrite bsize_he.
      inversion H4.
      -- intuition.
      -- eapply lteqBN_trans.
         ++ apply H4.
         ++ apply lteqs.
    * rewrite bsize_he.
      rewrite H.
      intuition.
  + assert(H6:=H).
    apply size_caseD in H.
    simpl in H6.
    simpl.
    rewrite H6.
    constructor.
    * assumption.
    * apply IHt2.
      assumption.
    * rewrite bsize_he.
      rewrite H.
      constructor.
    * rewrite bsize_he.
      rewrite H.
      constructor.
      intuition.
Qed.      

Lemma he_last: forall (t: BTree) (x:A),  
    lookup_bn (he x t) (bsize t) = x.
Proof.
intros.
pose proof (allBal t).
induction t.
+ simpl. reflexivity.
+ destruct (bbal_size_r a t1 t2).
  ++  simpl. simpl in H0.
      rewrite H0.
      inversion H.
      subst.
      simpl.
      apply (prop_0_U a t1 t2 (bsize t2)) in H.
      - destruct H.
        rewrite <-H.
        apply IHt1.
        assumption.
      - assumption.
  ++ simpl. simpl in H0.
      rewrite H0.
      simpl. apply IHt2.
      inversion H.
      assumption.
Qed.
     


Lemma he_idx: forall (t:BTree),  bbal t -> 
forall (j:BN), j <BN (bsize t) -> forall (x:A), lookup_bn (he x t) j = lookup_bn t j.
Proof.
intro.
intro.
induction t.
- intros. simpl.
  inversion H0.
- intros. 
  destruct (bbal_size_r a t1 t2).
  + simpl. 
    simpl in H1.
    rewrite H1.
    simpl.
    destruct j as [  |  a0 | b0].
    * reflexivity.
    * simpl in H0.
      rewrite H1 in H0.
      inversion H0.
      inversion H.
      subst.
      apply IHt1.
      assumption.
      apply (prop_0_U a t1 t2 (bsize t2)) in H1.
      destruct H1.
      rewrite H1.
      assumption.
      assumption.
    * reflexivity.
  + simpl in H1.
    simpl. rewrite H1.
    simpl.
    destruct j as [  |  a0 | b0].
    * reflexivity.
    * reflexivity.
    * simpl in H0.
      rewrite H1 in H0.
      inversion H0.
      inversion H.
      subst.
      apply IHt2.
      ** assumption.
      ** assumption.
Qed.      
(** 7.- Ejercicios de tarea*)


(** 1.-*)
Fixpoint lr (t1:BTree) : BTree :=
 match t1 with
  | E => undefBTree
  | N x l r => match l with
               | E => E
               | N y _ _ => N y r (lr l)
               end
 end.

Fixpoint hr (t1:BTree) : BTree  :=
 match t1 with
  | E => undefBTree
  | N x l r => match l with 
               | E => E
               | _ => match bsize t1 with 
                      | U b => N x l (hr r)
                      | D b => N x (hr l) r
                      |   Z => undefBTree 
                      end
               end
 end.
(** 2.-*)
Proposition bsize_lr_pred_bsize:
  forall (t:BTree), t<>E ->
    bsize (lr t) = predBN (bsize t).
Proof.
intros.
pose proof (allBal t).
induction t as [| a l IHl r].
- contradict H. reflexivity.
- inversion H0.
  subst.
  simpl (predBN (bsize (N a l r))).
  rewrite predsucBNinv.
  destruct l. 
    + apply leftE_leaf in H0.
       rewrite H0.
       simpl.
       reflexivity.
       reflexivity.
    + simpl (bsize (lr (N a (N a0 l1 l2) r))).
       simpl in IHl.
       rewrite IHl.
       3: assumption.
       2: intro W1; inversion W1.
       rewrite plusSuc_2.
       rewrite predsucBNinv.
       simpl.
       rewrite plusComm.
       reflexivity.
Qed.       
  

  
(** 3.-*)
Proposition bbal_bbal_lr:
  forall (t:BTree), t<> E->
    bbal t -> bbal (lr t).
Proof.
intros.
induction t as [| a l IHl r].
- contradict H; reflexivity.
- inversion H0.
  subst.
  destruct l.
  + apply leftE_leaf in H0.
    2: reflexivity.
    rewrite H0.
    simpl.
    constructor.
  + apply bbalN. 
    ++ assumption.
    ++ apply IHl.
       intro W; inversion W.
       assumption.
       
    ++ fold lr. 
       apply lteqBN_suc_pred in H7.
       rewrite <- bsize_lr_pred_bsize in H7.
       simpl in H7.
       assumption.
       intro W; inversion W.
       apply bsize_nonZ.
       intro W; inversion W.
    ++ fold lr. 
       assert ( 
        sucBN (predBN (bsize (N a0 l1 l2)))
         = bsize (N a0 l1 l2)) as W.
        { apply  sucpredBNinv. 
         apply bsize_nonZ.
         intro W; inversion W. }
        rewrite <- bsize_lr_pred_bsize in W.
        rewrite <- W in H6.
    simpl ( lr (N a (N a0 l1 l2) r)).
    exact H6. 
    intro W0; inversion W0.
Qed.
    

(** 4.-*)
Proposition lkp_lr_lkp_suc:
  forall (t:BTree)(j:BN), t<> E -> j <BN bsize (lr t) ->
    lookup_bn (lr t) j = lookup_bn t (sucBN j) .
Proof.
intros.
generalize dependent j.
pose proof (allBal t) as B.
induction t as [| a l IHl r].
(* base *)
intros.
contradict H; reflexivity.
+ intros j J.
  destruct  l.
  ++ apply leftE_leaf in B.
     2: reflexivity.
     rewrite B in J.
     simpl in J.
     inversion J.
  ++  remember (N a0 l1 l2) as l.
      destruct j.
      - rewrite Heql.
        simpl.
        reflexivity.
      - rewrite Heql.
        simpl.
        reflexivity.
      - rewrite Heql in IHl.
        remember (bsize (lr (N a0 l1 l2))) as s.
        simpl  in IHl.
        rewrite Heql.
        simpl (lookup_bn (lr (N a (N a0 l1 l2) r)) (D j)).
        rewrite IHl.
        reflexivity.
        -- intro X; inversion X.
        -- inversion B.
           rewrite <- Heql.
           assumption.
        -- rewrite bsize_lr_pred_bsize in J.
           2: intro X; inversion X.
           simpl in J.
           rewrite predsucBNinv in J. 
       simpl.
       rewrite Heqs.
       rewrite <-Heql.
       rewrite bsize_lr_pred_bsize.
       (* esta meta sale sin deestructuración pero
          requiere lemas del orden en la suma*)
       assert (bsize l <> Z ) as A1.
       { rewrite Heql.
         simpl.
         apply not_eq_sym.
         apply ZnotSucBN. }
       assert (l<>E) as A2.
       { rewrite Heql.
         intro X; inversion X.
        }
       clear IHl IHr Heqs.
       destruct (bbal_size_r a l r).
       3: { rewrite Heql.
            intro X; inversion X. }
       {  
         apply (size_caseU a l r (bsize r)) in H0 as W.
         rewrite <- W in J.
         rewrite <-( sucpredBNinv (bsize l)) in J.
       2: assumption.
       rewrite <-plusSuc_2 in J.
       rewrite plus_D in J.
       inversion J.
       assumption. }
       { 
         apply (size_caseD a l r (bsize r)) in H0 as W.
         rewrite W.
         rewrite predsucBNinv.
         rewrite W in J.
         rewrite <- plusSuc in J.
         rewrite plus_U in J.
         inversion J.
         assumption. }
Qed.

(** 5.-*)
Proposition lr_le_inv:
  forall (t:BTree)(x:A),
    lr (le x t) = t.
Proof.
intro.
induction t.
simpl. reflexivity.
intros.
simpl (le x (N a t1 t2)).
simpl.
pose proof (le_hasroot a t2).
rewrite IHt2.
destruct H.
destruct H.
rewrite H.
reflexivity.
Qed.

(** 6.-*)
Proposition le_lkp_lr_inv:
  forall (t:BTree), t<> E ->
    le (lookup_bn t Z) (lr t)=t.
Proof.
intros.
pose proof (allBal t).
induction t as [| a l IHl r].
contradict H.
reflexivity.
simpl.
destruct l.
- simpl. 
  apply leftE_leaf in H0.
  2: reflexivity.
  rewrite H0.
  reflexivity.
- inversion H0.
  subst.
  simpl (le a (N a0 r (lr (N a0 l1 l2)))).
  rewrite <-IHl.
  simpl.
  reflexivity.
  intro W; inversion W.
  assumption.
Qed.

(** 7.-*)
Proposition bsize_hr_pred_bsize:
  forall (t:BTree), t<> E ->
    bsize (hr t)= predBN (bsize t).
Proof.
intros.
pose proof (allBal t).
induction t as [| a l IHl r].
contradict H. reflexivity.
inversion H0.
subst.
simpl (predBN (bsize (N a l r))).
rewrite predsucBNinv.
destruct (bbal_size_r a l r).
+ apply (size_caseU a l r (bsize r)) in H1 as W.
  simpl.
  simpl in H1.
  rewrite H1.
  destruct l.
  ++ rewrite <-W.
     simpl.
     reflexivity.
  ++ simpl (bsize (N a (N a0 l1 l2) (hr r))).
     assert (r<>E) as NE. {
     apply bsize_nonZ.
     rewrite <-W.
     simpl.
     apply not_eq_sym.
     apply  ZnotSucBN. }
     rewrite IHr.
     
     rewrite plusSuc_2.
     rewrite sucpredBNinv.
     reflexivity.
     apply bsize_nonZ.
     assumption.
     assumption.
     assumption.
+ apply (size_caseD a l r (bsize r)) in H1 as W.
  simpl.
  simpl in H1.
  rewrite H1.
  destruct l.
  ++ simpl in W. 
     contradict W.
     apply ZnotSucBN.
  ++ 
     simpl (bsize (N a (hr (N a0 l1 l2)) r)).
     simpl in IHl.
     rewrite IHl.
     rewrite predsucBNinv.
     simpl.
     rewrite plusSuc.
     reflexivity.
     intro w;inversion w.
     assumption.
Qed.     

(** 8.-*)
Proposition bbal_bbal_hr:
  forall (t:BTree), t<>E->
    bbal t -> bbal (hr t).
Proof.
intros.
induction t as [| a l IHl r].
contradict H; reflexivity.
destruct (bbal_size_r a l r).
- simpl.
  apply (size_caseU a l r (bsize r)) in H1 as W.
  simpl in H1.
  rewrite H1.
  inversion H0.
     subst.
  destruct l.
  -- constructor.
  -- assert (r<> E) as Q.
     {
     apply bsize_nonZ.
     rewrite <-W.
     simpl.
     apply not_eq_sym.
     apply  ZnotSucBN. }
     constructor.
     assumption.
     apply IHr.
     apply Q.
     assumption.

     + rewrite bsize_hr_pred_bsize.
       rewrite <- W.
       simpl.
       rewrite predsucBNinv.
       apply lteqs.
       assumption.
     + rewrite bsize_hr_pred_bsize.
       rewrite W.
       rewrite sucpredBNinv.
       constructor.
       apply bsize_nonZ.
       assumption.
       assumption .
- simpl.
  simpl in H1.
  rewrite H1.
  inversion H0.
  subst.
  apply size_caseD in H1.
  destruct l.
  constructor.
  2: apply a.
  constructor.
  apply IHl.
  intro w; inversion w.
  assumption.
  assumption.
  + rewrite bsize_hr_pred_bsize.
    2: intro w; inversion w.
    rewrite H1.
    rewrite predsucBNinv.
    constructor.
  + rewrite bsize_hr_pred_bsize.
     2: intro w; inversion w.
     rewrite H1.
     rewrite predsucBNinv.
     apply lteqs.
Qed.

(** 9.-*)
Proposition lkp_hr_lkp:
  forall (t:BTree)(j:BN),t<>E-> j<BN bsize (hr t)->
    lookup_bn (hr t) j = lookup_bn t j.
Proof.
intros.
generalize dependent j.
pose proof (allBal t) as B.
induction t as [| a l IHl r].
(* base *)
contradict H; reflexivity.
(* inductivo*)
destruct (bbal_size_r a l r).
+ apply (size_caseU a l r (bsize r)) in H0 as W.
  simpl; simpl in H0.
  rewrite H0.
  destruct l.
  - intros j J.
    simpl in J.
    inversion J.
  - remember (N a0 l1 l2) as l.
    assert (r<>E) as X. {
     rewrite Heql in W.
     apply bsize_nonZ.
     rewrite <-W.
     simpl.
     apply not_eq_sym.
     apply  ZnotSucBN. }
     
    intros j J.
    rewrite Heql.
    simpl.
    destruct j.
      * reflexivity.
      * reflexivity.
      * rewrite IHr.
        reflexivity.
        exact X.
        inversion B.
        assumption.
       simpl in J.
       rewrite W in J.
       rewrite <- (sucpredBNinv (bsize r))in J.
(*        rewrite <- plusSuc in J. *)
       rewrite bsize_hr_pred_bsize in J.
       rewrite plus_D in J.
       inversion J.
       rewrite bsize_hr_pred_bsize.
       assumption.
       exact X.
       exact X.
       rewrite <-bsize_nonZ.
       exact X.
+   
  apply (size_caseD a l r (bsize r)) in H0 as W.
  simpl; simpl in H0.
  rewrite H0.
  destruct l.
  - intros j J.
    simpl in J.
    inversion J.
  - intros j J.
    
    (* remember (N a0 l1 l2) as l .*)
    destruct j.
      * simpl.  
       reflexivity.
      * rewrite <- IHl.
        -- simpl. reflexivity.
        -- intro S; inversion S.
        -- inversion B; assumption.
        -- remember (N a0 l1 l2) as l .
           simpl in J.
           rewrite bsize_hr_pred_bsize in J.
           rewrite <- (predsucBNinv (bsize r))in J.
           rewrite <- W in J.
           rewrite plus_U in J.
           inversion J.
           rewrite bsize_hr_pred_bsize.
           assumption.
           ++ rewrite Heql.
              intro X. discriminate X.
           ++ rewrite Heql.
              intro X. discriminate X.
              
      * simpl. reflexivity.
Qed.

(** 10.-*)
Proposition hr_he_inv:
  forall (t:BTree)(x:A),
    hr (he x t)=t.
Proof.
intros.
simpl.
induction t as [| a l IHl r].
simpl. reflexivity.
intros.
destruct (bbal_size_r a l r).
- simpl. simpl in H.
  rewrite H.
  simpl.
  pose proof (he_hasroot x l).
  destruct H0.
  destruct H0.
  destruct H0.
  rewrite H0.
  rewrite <- H0.
  rewrite bsize_he.
  rewrite <- plusSuc.
  rewrite H.
  simpl.
  rewrite IHl.
  reflexivity.
- simpl. simpl in H.
  rewrite H.
  simpl.
  pose proof (he_hasroot x r).
  destruct H0.
  destruct H0.
  destruct H0.
  rewrite H0.
  rewrite <- H0.
  rewrite bsize_he.
  rewrite <- plusSuc_2.
  rewrite H.
  simpl.
  rewrite IHr.
  
  pose proof (allBal (N a l r)) as W.
  inversion W.
  subst.
  destruct l.
  apply leftE_leaf in W.
  2: reflexivity.
  2: reflexivity.
   rewrite W in H.
   simpl in H.
   discriminate H.
Qed.

(** 11.-*)
Proposition he_lkp_pred_bsize_hr_inv:
  forall (t:BTree), t<>E->
    he(lookup_bn t (predBN (bsize t))) (hr t)=t.
Proof.
intros.
pose proof (allBal t) as B.
induction t as [| a l IHl r].
contradict H; reflexivity.

destruct (bbal_size_r a l r).
+ apply (size_caseU a l r (bsize r)) in H0 as W.
  destruct l.
  ++  simpl in H0.
  simpl.
  rewrite predsucBNinv.
(*   rewrite H0. *)
  rewrite <-W.
  simpl.
  simpl in W.
  symmetry in W.
  apply bsize_Z in W.
  rewrite W.
  reflexivity.
  ++ remember (N a0 l1 l2) as l.
    assert (bsize r<>Z) as A1.
    {
     rewrite <-W.
    rewrite Heql.
    simpl.
    apply not_eq_sym.
    apply ZnotSucBN.
    }
    assert (r<>E) as A2.
    { apply bsize_nonZ; assumption . }
    assert (bsize l ⊞ bsize r = D(predBN (bsize r))).
    { 
    rewrite <- predBNUD.
    rewrite <-H0.
    simpl.
    rewrite predsucBNinv.
    reflexivity.
    assumption.
    }
    simpl.
    rewrite predsucBNinv.
    rewrite H1.
    rewrite <- H1.
    simpl in H0.
    rewrite H0.
    rewrite Heql.
    rewrite <- Heql.
    simpl.
    rewrite bsize_hr_pred_bsize.
    rewrite plusSuc_2.
    rewrite sucpredBNinv.
    rewrite H1.
    rewrite IHr.
    reflexivity.
    assumption.
    inversion B.
    assumption.
    assumption.
    assumption.
+ apply (size_caseD a l r (bsize r)) in H0 as W.
  destruct l.
  ++  simpl in H0.
      apply leftE_leaf in B.
      2: reflexivity.
      rewrite B in W.
      simpl in W.
      inversion W.
  ++ remember (N a0 l1 l2) as l.
    assert (bsize l<>Z) as A1.
    {
    rewrite W.
    apply not_eq_sym.
    apply ZnotSucBN.
    }
    assert (l<>E) as A2.
    { apply bsize_nonZ; assumption . }
     assert (bsize l ⊞ bsize r = U(predBN (bsize l))) as J.
    {
    rewrite W.
    rewrite <-plusSuc.
    rewrite predsucBNinv.
    apply  plus_U.
    }
    simpl.
    rewrite predsucBNinv.
    rewrite J.
    rewrite Heql.
    rewrite <- Heql.
    simpl (sucBN (U (predBN (bsize l)))).
    remember (he (lookup_bn l (predBN (bsize l)))) as s.
    
    simpl.
    rewrite Heqs. rewrite Heqs in IHl.
    simpl.
    rewrite bsize_hr_pred_bsize.
    rewrite plusSuc.
    rewrite sucpredBNinv.
    rewrite J.
    rewrite IHl.
    reflexivity.
    assumption.
    inversion B.
    assumption.
    assumption.
    assumption.
Qed.

      