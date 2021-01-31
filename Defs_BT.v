(** Tarea 3 Verificación Formal
    Luis B. Lluis LL11
    El siguiente script contiene las notaciones y definiciones 
    para árboles de braun.
    Este script es una concatenación 
    de scripts binary_tree.v , braunT_bn.v , lookupdBN.v , btExensions.v
    de Favio Ezequiel Miranda. 
    (* Contenido
  1.- bn2----------------no depends
      bn sucBN predBN toN toBN plusBN
     
  2.- binary_tree--------no depends
      BTree
     
  3.- orderbn------------depends bn2
      ltBN lteqBN
     
  4.- braunT_bn----------depends orderbn binary_tree
      bsize bbal 
      
  5.- lookupdBN----------depends braunT_bn
      lookup_bn update
      
  6.- btExtensions-------depends lookup 
      le he
      
*)*)

Add LoadPath "C:\Users\spide\Documents\Tareas\VerificacionFormal\Tareas\Tarea3\Tarea3VFLuisBLluis" as camino. 

Load Defs_BN . 
(* From Tarea3VF Require Import Defs_BN .  *)


(** 2.- binary_tree*)

Parameter (A:Type)
          (eq_dec_A: forall (x y:A),{x=y}+{x<>y})
          (undefA : A).
          
(* Binary trees defined here*)
Inductive BTree : Type :=
    E : BTree   
  | N : A -> BTree  -> BTree  -> BTree.    
Parameter (undefBTree : BTree).   

(** 4.- braunT_bn *)
(*size on binary trees defined next*)
Fixpoint bsize (t:BTree): BN :=
 match t with
  E => Z
 |N x s t =>  sucBN ((bsize s) ⊞ (bsize t))
 end.

(* Balance condition on Braun trees *)
Inductive bbal : BTree -> Prop:= 
 |bbalE : bbal E 
 |bbalN : forall (a: A) (s t: BTree), 
        bbal s -> bbal t -> 
        (bsize t) ≤BN (bsize s) -> 
        (bsize s) ≤BN (sucBN (bsize t)) -> 
                                      bbal (N a s t).
Parameter (allBal: forall (t:BTree), bbal t).

(** 5.- lookupdBN*)

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
(** 6.- btExtensions *)
Fixpoint le (x:A) (t:BTree) : BTree :=
 match t with
    E => N x E E
  | N y s t => N x (le y t) s
 end.

Fixpoint he (x:A) (t:BTree) : BTree  :=
 match t with
  |E => N x E E
  |N y l r => match bsize t with
               |U b => N y (he x l) r
               |D b => N y l (he x r)
               |  Z => undefBTree 
              end
 end.
 