Add LoadPath "C:\Users\spide\Documents\Tareas\VerificacionFormal\Tareas\Tarea3\Tarea3VFLuisBLluis" as camino. 

Load Defs_BN . 

(* From Tarea3VF Require Import Defs_BN .  *)


(** Tarea 3 Verificación Formal
    Luis B. Lluis LL11
    El siguiente script contiene las notaciones y definiciones 
    para árboles de braun.
    Este script es una concatenación 
    de scripts binary_tree.v , braunT_bn.v , lookupdBN.v , btExensions.v
    de Favio Ezequiel Miranda. 
    
    NOTA: las definiciones de lr y hr no se encuentran al final de este
    script pero comentadas pues se consideró más natural
    dejar todos los ejercios juntos de la tarea.
    Para una rápida localización se puede buscar la cadena "123".
    
  Contenido
     
  2.- binary_tree--------no depends
      BTree
     
  4.- braunT_bn----------depends orderbn binary_tree
      bsize bbal 
      
  5.- lookupdBN----------depends braunT_bn
      lookup_bn update
      
  6.- btExtensions-------depends lookup 
      le he
  7.- Tarea3VF-----------depends btExtensions
      lr he (comentados; buscar cadena 123)
      
*)




(** 2.-------------------- binary_tree-------------------*)

Parameter (A:Type)
          (eq_dec_A: forall (x y:A),{x=y}+{x<>y})
          (undefA : A).
          
(* Binary trees defined here*)
Inductive BTree : Type :=
    E : BTree   
  | N : A -> BTree  -> BTree  -> BTree.    
Parameter (undefBTree : BTree).   

(** 4.------------------- braunT_bn------------------ *)
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

(** 5.------------------- lookupdBN-------------------*)

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
(** 6.------------------- btExtensions------------------- *)
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

(** 7.-------------------- Tarea3VF-------------------*)
(** 1.-*)
(* Fixpoint lr (t:BTree) : BTree :=
 match t with
  | E => undefBTree
  | N x l r => match l with
               | E => E
               | N y _ _ => N y r (lr l)
               end
 end.

Fixpoint hr (t:BTree) : BTree  :=
 match t with
  | E => undefBTree
  | N x l r => match l with 
               | E => E
               | _ => match bsize t with 
                      | U b => N x l (hr r)
                      | D b => N x (hr l) r
                      |   Z => undefBTree 
                      end
               end
 end. *)
 