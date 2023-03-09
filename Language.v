(**

This file describes the representation of modelling language.

Author: Bowen Zhang.

Date : 2023.02.21
*)

From SLF (* TLC *) Require Export LibCore.
From SLF (* Sep *) Require Export TLCbuffer Var Fmap.

(* ###################### Syntax ###################### *)

Definition bloc : Type := nat.
Definition floc : Type := nat.

Definition fnull : floc := 0%nat.
Definition bnull : bloc := 0%nat.

(*---------- the block primitive operations ----------*)
Inductive bprim : Type :=
  | bprim_create   : bprim   
  | bprim_delete   : bprim   
  | bprim_get      : bprim   
  | bprim_size     : bprim  
  | bprim_append   : bprim    
  | bprim_trun     : bprim     
  | bMR_mapper     : bprim.     (* WordCount mapper *)

(*---------- the file primitive operations ----------*)
Inductive fprim : Type :=
  | fprim_create   : fprim 
  | fprim_delete   : fprim     
  | fprim_get      : fprim      
  | fprim_size     : fprim     
  | fprim_nthblk   : fprim    
  | fprim_set      : fprim    
  | fprim_attach   : fprim  
  | fprim_trun     : fprim  
  (*-- WordCount opertions --*)
  | fMR_merge      : fprim
  | fMR_group      : fprim
  | fMR_reducer    : fprim.

(*--------- arith operations -------------------*)
Inductive aprim : Type :=
  | val_eq  : aprim       (*a ?= b*)
  | val_add : aprim       (*a + b*)
  | val_min : aprim       (*a - b*)
  | val_le  : aprim.      (*a <= b*)


(*--------- WordCount values ---------*)
(* wordcount kvpair (word, times) *)
Definition wdpair : Type := int * int.

Inductive WCval : Type :=
  | WCval_listwdpair : list wdpair -> WCval
  | WCval_Listwd : (list (list wdpair)) -> WCval.

(*-------- some auxiliary list primitive operations (not important) --------*)
Inductive lprim : Type :=
  | val_list_rev     : lprim   (*reverse a list*)
  | val_list_len     : lprim   (*get the length of content*)
  | val_new_blist    : lprim   (*create a list of block locs*)
  | val_blist_buffer : lprim   (*gather a list of block locs*)
  | val_blist_rev    : lprim   (*reverse a list of block locs*)
  | val_list_hd_bk   : lprim   (*extract list for a block*)
  | val_list_tl_bk   : lprim   (*after extraction*)
  | val_list_hd      : lprim   (*extract list for a block*)
  | val_list_tl      : lprim   (*after extraction*)
  | val_list_app     : lprim   (*append a list*)
  | val_list_cut     : lprim   (*truncate a list*)
  | val_reform       : lprim   (*trans list to save*)
  | val_app_wdlist   : lprim.  (*append a word list*)

(*---------- the val and the term ----------*)
Inductive val : Type :=
  | val_unit     : val
  | val_bool     : bool -> val
  | val_int      : int -> val
  | val_listint  : list int -> val
  | val_listbloc : list bloc -> val
  | val_floc     : floc -> val
  | val_bloc     : bloc -> val
  | val_bprim    : bprim -> val
  | val_fprim    : fprim -> val
  | val_lprim    : lprim -> val
  | val_aprim    : aprim -> val
  | val_fun      : var -> trm -> val
  | val_fix      : var -> var -> trm -> val
  | val_WCval    : WCval -> val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if  : trm -> trm -> trm -> trm.

(* ##################### The Definition of CBS heap ##################### *)
(*------- the entire corresponding state -------*)
Definition stateb : Type := fmap bloc (list int).
Definition statef : Type := fmap floc (list bloc).
Definition state : Type := statef * stateb.

(*------- the part of corresponding state -------*)
Definition heapb : Type := stateb.
Definition heapf : Type := statef.
Definition heap : Type := state.

Notation "'hb_empty'" := (@Fmap.empty bloc (list int) )
  (at level 0).
Notation "'hf_empty'" := (@Fmap.empty floc (list bloc) )
  (at level 0).
Notation "'h_empty'" := (hf_empty,hb_empty)
  (at level 0).
Notation "h1 \u h2" := (Fmap.union h1 h2)
  (at level 37, right associativity).

(*** Implicit Types and coercions (to improve the readability) ***)

Implicit Types b  : bloc.
Implicit Types f  : floc.
Implicit Types ln : list int.
Implicit Types lb : list bloc.
Implicit Types n w : int.
Implicit Types v  : val.
Implicit Types t  : trm.
Implicit Types be : bool.
Implicit Types hb : heapb.
Implicit Types sb : stateb.
Implicit Types hf : heapf.
Implicit Types sf : statef.

Coercion val_bool  : bool >-> val.
Coercion val_floc  : floc >-> val.
Coercion val_bloc  : bloc >-> val.
Coercion val_lprim : lprim >-> val.
Coercion val_aprim : aprim >-> val.
Coercion val_WCval : WCval >-> val.
Coercion val_int   : Z >-> val.
Coercion val_bprim : bprim >-> val.
Coercion val_fprim : fprim >-> val.

Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.

(*** The substitution function ***)
(* -- subst var to val directly -- *)
Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if_y_eq x (trm_val w) t
  | trm_fun x t1 => trm_fun x (if_y_eq x t1 (aux t1))
  | trm_fix f x t1 => trm_fix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq  (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (if_y_eq x t2 (aux t2))
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  end.

Definition trm_is_val (t:trm) : Prop :=
  match t with trm_val v => True | _ => False end.

(**--------some Coq functions to handel lists--------**)
Definition droplast (n:nat) {A} (l:list A) : list A :=
  let l' := rev l in
  let l'' := drop n l' in
    rev l''.

Definition init (w:int) : wdpair := (w,1).

Definition app (l1 l2 : list wdpair) : list wdpair := List.app l1 l2.

Definition lwdhd (lwd:list wdpair) : wdpair := (nth_default (0,0) 0 lwd).

Definition eqword (p1 p2: wdpair) : bool := (fst p1) =? (fst p2).

Definition neqword (p1 p2: wdpair) : bool := negb (eqword p1 p2).

Definition neqlist (l1 l2:list wdpair) : bool := neqword (lwdhd l1) (lwdhd l2).

Fixpoint classify (l1 l2:list wdpair) : list (list wdpair) :=
  match l1,l2 with
  | nil,_ | _, nil => nil
  | x::l1',l2 => (List.filter (eqword x) l2) :: 
    (classify l1' l2) 
  end.

Definition remove (lwd:list wdpair) (Lwd:list (list wdpair)) : list (list wdpair) := 
 List.filter (neqlist lwd) Lwd.

Fixpoint remove_duplicates (L:list (list wdpair)) : list (list wdpair):=
  match L with
  | nil => nil
  | x::L' => x :: (remove x (remove_duplicates L'))
  end.

Definition addint (n1 n2:int) : int := n1+n2.

Definition inithd (a:wdpair) : wdpair := ((fst a), 0).

Definition addpair (a1 a2:wdpair) : wdpair := ((fst a1), (addint (snd a1) (snd a2) )).

Definition accmulate (lwd:list wdpair) : wdpair :=
  List.fold_right addpair (inithd (lwdhd lwd)) lwd.

Fixpoint kv2int (l:list wdpair) : (list int) :=
  match l with
  | nil => nil
  | (w,n) :: tl => w :: n :: (kv2int tl)
end.

(* ########################### The Evaluation Rules ########################### *)
Open Scope liblist_scope.
Open Scope Z_scope.

Inductive eval : heap -> trm -> heap -> val -> Prop :=
  (*------ trm eval to its value ------*)
  | eval_val_refine : forall sf sb v,
      eval (sf, sb) (trm_val v) (sf, sb) v
  | eval_val : forall s v,
      eval s (trm_val v) s v
  | eval_fun : forall s x t1,
      eval s (trm_fun x t1) s (val_fun x t1)
  | eval_fix : forall s F x t1,
      eval s (trm_fix F x t1) s (val_fix F x t1)

  (*------   arith prim operation    ------*)
  | eval_add : forall s n1 n2,
      eval s (val_add n1 n2) s (n1 + n2)
  | eval_min : forall s n1 n2,
      eval s (val_min n1 n2) s (n1 - n2)
  | eval_le : forall s n1 n2,
      eval s (val_le n1 n2) s (val_bool (isTrue (n1 <= n2)))
  | eval_eq : forall s n1 n2,
      eval s (val_eq n1 n2) s (val_bool (n1 =? n2))

  (*------   aux prim operation    ------*)
  | eval_list_rev : forall s ln1,
      eval s (val_list_rev (val_listint ln1)) s (val_listint (rev ln1))
  | eval_list_hd : forall s ln1,
      eval s (val_list_hd (val_listint ln1)) s (val_listint (LibList.take 1%nat ln1))
  | eval_list_tl : forall s ln1,
      eval s (val_list_tl (val_listint ln1)) s (val_listint (LibList.drop 1%nat ln1))
  | eval_list_hd_blk : forall s ln1,
      eval s (val_list_hd_bk (val_listint ln1)) s (val_listint (LibList.take 2%nat ln1))
  | eval_list_tl_blk : forall s ln1,
      eval s (val_list_tl_bk (val_listint ln1)) s (val_listint (LibList.drop 2%nat ln1))
  | eval_list_len : forall s ln1,
      eval s (val_list_len (val_listint ln1)) s (LibList.length ln1)  
  | eval_list_app : forall s ln1 ln2,
      eval s (val_list_app (val_listint ln1) (val_listint ln2)) 
           s (val_listint (ln1 ++ ln2))
  | eval_blist_rev : forall sf sb bl,
      eval (sf, sb) (val_blist_rev (val_listbloc bl)) (sf, sb) (val_listbloc (LibList.rev bl))
  | eval_new_blist : forall sf sb b,
      eval (sf, sb) (val_new_blist (val_bloc b)) (sf, sb) (val_listbloc (b::nil))
  | eval_blist_buffer : forall sf sb b lb,
      eval (sf, sb) (val_blist_buffer (val_bloc b) (val_listbloc lb)) (sf, sb) (val_listbloc (b::lb))


  (*--------- block prim operation ---------*)
  | eval_bcreate : forall sf sb b ln,
      ~ Fmap.indom sb b ->
      eval (sf, sb) (bprim_create (val_listint ln)) (sf, (Fmap.update sb b ln)) b

  | eval_bget : forall sf sb b,
      Fmap.indom sb b ->
      eval (sf, sb) (bprim_get (val_bloc b)) (sf, sb) (val_listint (Fmap.read sb b))

  | eval_bdelete : forall sf sb b,
      Fmap.indom sb b ->
      eval (sf, sb) (bprim_delete (val_bloc b)) (sf, (Fmap.remove sb b)) val_unit

  | eval_bsize : forall sf sb b,
      Fmap.indom sb b ->
      eval (sf, sb) (bprim_size (val_bloc b))
           (sf, sb) (val_int (List.length (Fmap.read sb b)))

  | eval_btruncate : forall sf sb b n,
      Fmap.indom sb b ->
      eval (sf, sb) (bprim_trun (val_bloc b) n) 
        (sf, (Fmap.update sb b (droplast (Z.to_nat n) (Fmap.read sb b) )))  val_unit

  | eval_bappend_list : forall sf sb b ln,
      Fmap.indom sb b ->
      eval (sf, sb) (bprim_append (val_bloc b) (val_listint ln)) 
        (sf, (Fmap.update sb b ((Fmap.read sb b) ++ ln) ))  val_unit

 (*----------- file prim operation -----------*)
  | eval_fcreate : forall sf sb f lb,
      ~ Fmap.indom sf f ->
      eval (sf, sb) (fprim_create (val_listbloc lb))
        ((Fmap.update sf f lb), sb) (val_floc f)

  | eval_fget : forall sf sb f,
      Fmap.indom sf f ->
      eval (sf, sb) (fprim_get (val_floc f)) (sf, sb) (val_listbloc (Fmap.read sf f))

  | eval_fsize : forall sf sb f,
      Fmap.indom sf f ->
      eval (sf, sb) (fprim_size (val_floc f))
           (sf, sb) (val_int (List.length (Fmap.read sf f)))

  | eval_fget_nth_blk : forall sf sb f n,
      Fmap.indom sf f ->
      eval (sf, sb) (fprim_nthblk (val_floc f) n) (sf, sb)
           (val_bloc (nth_default bnull (Z.to_nat n) (Fmap.read sf f)))

  | eval_fset_nth_blk : forall sf sb f n b,
      Fmap.indom sf f ->
      eval (sf, sb) (fprim_set (val_floc f) n (val_bloc b))
           (Fmap.update sf f (LibList.update (to_nat n) b (Fmap.read sf f)), sb) val_unit
  
  | eval_fattach: forall sf sb f lb,
      Fmap.indom sf f ->
      eval (sf, sb) (fprim_attach (val_floc f) (val_listbloc lb)) 
       ((Fmap.update sf f ( (Fmap.read sf f) ++ lb )), sb) val_unit
  
  | eval_fdelete : forall sf sb f,
      Fmap.indom sf f ->
      eval (sf, sb) (fprim_delete (val_floc f)) ( (Fmap.remove sf f), sb) val_unit

  | eval_ftruncate : forall sf sb f n,
      Fmap.indom sf f ->
      eval (sf, sb) (fprim_trun (val_floc f) n) 
        ( (Fmap.update sf f (droplast (Z.to_nat n) (Fmap.read sf f) )), sb) val_unit

  (*------------ trm rules ------------*)
   | eval_app_args : forall s1 s2 s3 s4 t1 t2 v1 v2 r,
      (~ trm_is_val t1 \/ ~trm_is_val t2) ->
      eval s1 t1 s2 v1 ->
      eval s2 t2 s3 v2 ->
      eval s3 (trm_app v1 v2) s4 r ->
      eval s1 (trm_app t1 t2) s4 r
   | eval_app_fun : forall s1 s2 v1 v2 x t1 v,
      v1 = val_fun x t1 ->
      eval s1 (subst x v2 t1) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
   | eval_app_fix : forall s1 s2 v1 v2 F x t1 v,
      v1 = val_fix F x t1 ->
      eval s1 (subst x v2 (subst F v1 t1)) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
   | eval_seq : forall s1 s2 s3 t1 t2 v1 v,
      eval s1 t1 s2 v1 ->
      eval s2 t2 s3 v ->
      eval s1 (trm_seq t1 t2) s3 v
   | eval_let : forall s1 s2 s3 x t1 t2 v1 r,
      eval s1 t1 s2 v1 ->
      eval s2 (subst x v1 t2) s3 r ->
      eval s1 (trm_let x t1 t2) s3 r
   | eval_if : forall s1 s2 be v t1 t2,
      eval s1 (if be then t1 else t2) s2 v ->
      eval s1 (trm_if (val_bool be) t1 t2) s2 v

  (*----- evaluation rules for MapReduce ------*)

  (*-- mapper --*)
  | eval_mapper : forall sf sb b,
      Fmap.indom sb b ->
      eval (sf, sb) (bMR_mapper b) (sf, sb) 
        (WCval_listwdpair (List.map init (Fmap.read sb b)))

  (*-- reducer --*)
  | eval_merge : forall s Lwd,
      eval s (fMR_merge (WCval_Listwd Lwd)) s (WCval_listwdpair (fold_right app nil Lwd))

  | eval_group : forall s lwd,
      eval s (fMR_group (WCval_listwdpair lwd)) s 
        (WCval_Listwd (remove_duplicates (classify lwd lwd)))

  | eval_wdreduce : forall s Lwd,
      eval s (fMR_reducer (WCval_Listwd Lwd)) s (WCval_listwdpair (List.map accmulate Lwd))


  (*-- aux rules for list operation in MapReduce --*)
  | eval_app_wdlist : forall s lwd Lwd,
      eval s (val_app_wdlist (WCval_listwdpair lwd) (WCval_Listwd Lwd)) 
           s (WCval_Listwd (lwd :: Lwd))

  | eval_reform : forall s lwd,
      eval s (val_reform (WCval_listwdpair lwd)) s 
        (val_listint (kv2int lwd)).


(*  --------------- some relation about terms --------------- *)
Definition eval_like (t1 t2:trm) : Prop :=
  forall s s' v, eval s t1 s' v -> eval s t2 s' v.

Definition trm_equiv (t1 t2:trm) : Prop :=
  forall s s' v, eval s t1 s' v <-> eval s t2 s' v.

Lemma eval_like_eta_reduction : forall (t:trm) (x:var),
  eval_like t (trm_let x t x).
Proof using.
  introv R. applys eval_let R.
  simpl. rewrite var_eq_spec. case_if. apply eval_val.
Qed.

Lemma eval_like_eta_expansion : forall (t:trm) (x:var),
  eval_like (trm_let x t x) t.
Proof using.
  introv R. inverts R as. introv R1 R2.
  simpl in R2. rewrite var_eq_spec in R2. case_if.
  inverts R2; apply R1.
Qed.

Lemma trm_equiv_eta : forall (t:trm) (x:var),
  trm_equiv t (trm_let x t x).
Proof using.
  intros. intros s s' v. iff M.
  { applys eval_like_eta_reduction M. }
  { applys eval_like_eta_expansion M. }
Qed.

(* ################### evaluation rule in SL style ############################## *)

(*----------- block prim operations -----------*)

Lemma eval_bcreate_sep : forall sf sb1 sb2 ln b,
  sb2 = Fmap.single b ln ->
  Fmap.disjoint sb2 sb1 ->
  eval (sf, sb1) (bprim_create (val_listint ln))
       (sf, (Fmap.union sb2 sb1)) (val_bloc b).
Proof.
  introv -> M. forwards Db: Fmap.indom_single b ln.
  rewrite <- Fmap.update_eq_union_single.
  apply~ eval_bcreate.
  { intros N. applys~ Fmap.disjoint_inv_not_indom_both M N. }
Qed.

Lemma eval_bget_sep : forall sf sb sb2 b ln,
  sb = Fmap.union (Fmap.single b ln) sb2 ->
  eval (sf, sb) (bprim_get (val_bloc b))
       (sf, sb) (val_listint ln).
Proof.
  introv ->. forwards Dv: Fmap.indom_single b ln.
  applys_eq eval_bget 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_bsize_sep : forall sf sb sb2 b ln,
  sb = Fmap.union (Fmap.single b ln) sb2 ->
  eval (sf, sb) (bprim_size (val_bloc b))
       (sf, sb) (List.length ln).
Proof.
  introv ->. forwards Dv: Fmap.indom_single b ln.
  applys_eq eval_bsize 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_bdelete_sep : forall sf sb1 sb2 b ln,
  sb1 = Fmap.union (Fmap.single b ln) sb2 ->
  Fmap.disjoint (Fmap.single b ln) sb2 ->
  eval (sf, sb1) (bprim_delete (val_bloc b))
       (sf, sb2) val_unit.
Proof.
  introv -> D. forwards Db: Fmap.indom_single b ln.
  applys_eq eval_bdelete 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.remove_union_single_l.
    intros D1. applys~ Fmap.disjoint_inv_not_indom_both D D1. }
Qed.

Lemma eval_btruncate_sep : forall sf sb1 sb2 sb b ln1 n,
  sb1 = Fmap.union (Fmap.single b ln1) sb ->
  sb2 = Fmap.union (Fmap.single b (droplast (Z.to_nat n) ln1)) sb ->
  Fmap.disjoint (Fmap.single b ln1) sb ->
  eval (sf, sb1) (bprim_trun (val_bloc b) n)
       (sf, sb2) val_unit.
Proof.
  introv -> -> D. forwards Db: Fmap.indom_single b ln1.
  applys_eq eval_btruncate 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite Fmap.read_union_l, Fmap.read_single; auto.
    rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single.  }
Qed.

Lemma eval_bappend_sep : forall sf sb1 sb2 sb bp ln1 ln2,
  sb1 = Fmap.union (Fmap.single bp ln1) sb ->
  sb2 = Fmap.union (Fmap.single bp (ln1++ln2)) sb ->
  Fmap.disjoint (Fmap.single bp ln1) sb ->
  eval (sf, sb1) (bprim_append (val_bloc bp) (val_listint ln2))
       (sf, sb2) val_unit.
Proof.
  introv -> -> D. forwards Db: Fmap.indom_single bp ln1.
  applys_eq eval_bappend_list 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite Fmap.read_union_l, Fmap.read_single; auto.
    rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single. }
Qed.

(*--------- file prim operations ---------*)

Lemma eval_fcreate_sep : forall sf1 sb sf2 lb f,
  sf2 = Fmap.single f lb ->
  Fmap.disjoint sf2 sf1 ->
  eval (sf1, sb) (fprim_create (val_listbloc lb))
       ((Fmap.union sf2 sf1), sb) (val_floc f).
Proof.
  introv -> D. forwards Db: Fmap.indom_single f lb.
  rewrite <- Fmap.update_eq_union_single.
  apply eval_fcreate.
  { intros N. applys~ Fmap.disjoint_inv_not_indom_both D N. }
Qed. 

Lemma eval_fsize_sep : forall sf sb sf2 f lb,
  sf = Fmap.union (Fmap.single f lb) sf2 ->
  eval (sf, sb) (fprim_size (val_floc f))
       (sf, sb) (List.length lb).
Proof.
  introv ->. forwards Dv: Fmap.indom_single f lb.
  applys_eq eval_fsize 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_fget_sep : forall sf sb sf2 lb f,
  sf = Fmap.union (Fmap.single f lb) sf2 ->
  eval (sf, sb) (fprim_get (val_floc f))
       (sf, sb) (val_listbloc lb).
Proof.
  introv ->. forwards Df: Fmap.indom_single f lb.
  applys_eq eval_fget 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_fget_nth_blk_sep : forall sf sb sf2 lb f n,
  sf = Fmap.union (Fmap.single f lb) sf2 ->
  eval (sf, sb) (fprim_nthblk (val_floc f) n)
       (sf, sb) (val_bloc (nth_default bnull (Z.to_nat n) lb)).
Proof.
  introv ->. forwards Df: Fmap.indom_single f lb.
  applys_eq eval_fget_nth_blk 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_fset_nth_blk_sep : forall sf sb sf1 sf2 lb f n b,
  sf1 = Fmap.union (Fmap.single f lb) sf ->
  sf2 = Fmap.union (Fmap.single f (LibList.update (to_nat n) b lb)) sf ->
  Fmap.disjoint (Fmap.single f lb) sf ->
  eval (sf1, sb) (fprim_set (val_floc f) n (val_bloc b))
       (sf2, sb) (val_unit).
Proof.
  introv -> -> D. forwards Df: Fmap.indom_single f lb.
  applys_eq eval_fset_nth_blk 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single.
    rewrite~ Fmap.read_union_l. 
    rewrite~ Fmap.read_single. }
Qed.

Lemma eval_fdelete_sep : forall sf1 sb sf2 lb f,
  sf1 = Fmap.union (Fmap.single f lb) sf2 ->
  Fmap.disjoint (Fmap.single f lb) sf2 ->
  eval (sf1, sb) (fprim_delete (val_floc f))
       (sf2, sb) val_unit.
Proof.
  introv -> D. forwards Df: Fmap.indom_single f lb.
  applys_eq eval_fdelete 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.remove_union_single_l. intros D1.
    applys~  Fmap.disjoint_inv_not_indom_both D D1. }
Qed.

Lemma eval_fattach_sep : forall sf sf1 sf2 sb f lb1 lb2,
  sf1 = Fmap.union (Fmap.single f lb1) sf ->
  sf2 = Fmap.union (Fmap.single f (lb1++lb2)) sf ->
  Fmap.disjoint (Fmap.single f lb1) sf ->
  eval (sf1, sb) (fprim_attach (val_floc f) (val_listbloc lb2))
       (sf2, sb) val_unit.
Proof.
  introv -> -> D. forwards Db: Fmap.indom_single f lb1.
  applys_eq eval_fattach 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite Fmap.read_union_l, Fmap.read_single; auto.
    rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single. }
Qed.

Lemma eval_ftruncate_sep : forall sf sf1 sf2 sb f lb n,
  sf1 = Fmap.union (Fmap.single f lb) sf ->
  sf2 = Fmap.union (Fmap.single f (droplast (Z.to_nat n) lb)) sf ->
  Fmap.disjoint (Fmap.single f lb) sf ->
  eval (sf1, sb) (fprim_trun (val_floc f) n)
       (sf2, sb) val_unit.
Proof.
  introv -> -> D. forwards Db: Fmap.indom_single f lb.
  applys_eq eval_ftruncate 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite Fmap.read_union_l, Fmap.read_single; auto.
    rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single. }
Qed.

(* ################### evaluation MR rule in SL style ############################## *)

Lemma eval_wdmap_sep : forall sf sb sb2 b ln,
  sb = Fmap.union (Fmap.single b ln) sb2 ->
  eval (sf, sb) (bMR_mapper (val_bloc b))
       (sf, sb) (WCval_listwdpair (List.map init ln)).
Proof.
  introv ->. forwards Dv: Fmap.indom_single b ln.
  applys_eq eval_mapper 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

(*==============================================================*)
(* ############ Notations of the language (to improve the readability) #################### *)
Module NotationForTrm.

(** ** Notation for terms *)
Notation "'If_' t0 'Then' t1 'Else' t2" :=
  (trm_if t0 t1 t2)
  (at level 69, t0 at level 0) : trm_scope.

Notation "'If_' t0 'Then' t1 'End'" :=
  (trm_if t0 t1 val_unit)
  (at level 69, t0 at level 0) : trm_scope.

Notation "'Let' x ':=' t1 'in' t2" :=
  (trm_let x t1 t2)
  (at level 69, x at level 0, right associativity,
  format "'[v' '[' 'Let'  x  ':='  t1  'in' ']'  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "t1 '';' t2" :=
  (trm_seq t1 t2)
  (at level 68, right associativity,
   format "'[v' '[' t1 ']'  '';'  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "'Fix' f x1 ':=' t" :=
  (val_fix f x1 t)
  (at level 69, f, x1 at level 0, format "'Fix'  f  x1  ':='  t") : val_scope.

Notation "'Fix' f x1 x2 ':=' t" :=
  (val_fix f x1 (trm_fun x2 t))
  (at level 69, f,x1, x2 at level 0, format "'Fix'  f x1 x2 ':=' t") : val_scope.

Notation "'Fix' f x1 x2 x3 ':=' t" :=
  (val_fix f x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, f,x1, x2, x3 at level 0, format "'Fix'  f x1 x2 x3 ':=' t") : val_scope.

Notation "'Fix_' f x1 ':=' t" :=
  (trm_fix f x1 t)
  (at level 69, f, x1 at level 0, format "'Fix_'  f  x1  ':='  t") : trm_scope.

Notation "'Fun' x1 ':=' t" :=
  (val_fun x1 t)
  (at level 69, x1 at level 0, format "'Fun'  x1  ':='  t") : val_scope.

Notation "'Fun' x1 x2 ':=' t" :=
  (val_fun x1 (trm_fun x2 t))
  (at level 69, x1, x2 at level 0, format "'Fun' x1 x2 ':=' t") : val_scope.

Notation "'Fun' x1 x2 x3 ':=' t" :=
  (val_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, x1, x2, x3 at level 0, format "'Fun' x1 x2 x3 ':=' t") : val_scope.

Notation "'Fun_' x1 ':=' t" :=
  (trm_fun x1 t)
  (at level 69, x1 at level 0, format "'Fun_'  x1  ':='  t") : trm_scope.

Notation "'Fun_' x1 x2 ':=' t" :=
  (trm_fun x1 (trm_fun x2 t))
  (at level 69, x1, x2 at level 0, format "'Fun_' x1 x2 ':=' t") : trm_scope.

Notation "'Fun_' x1 x2 x3 ':=' t" :=
  (trm_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, x1, x2, x3 at level 0, format "'Fun_' x1 x2 x3 ':=' t") : trm_scope.

(* ----------Notations of file prim---------------- *)
Notation "'fcreate lb" :=
  (fprim_create lb)
  (at level 67) : trm_scope.

Notation "'fatt b lb" :=
  (fprim_attach b lb)
  (at level 67,b at level 0,format "''fatt' b lb").

Notation "'set f n 'as b" :=
  (fprim_set f n b)
  (at level 67, f,b at level 0,format "''set' f n ''as' b") : trm_scope.

Notation "'fsize f" :=
  (fprim_size f)
  (at level 67) : trm_scope.

Notation "'fdelete f" :=
  (fprim_delete f)
  (at level 67) : trm_scope.

Notation "'ftrun f n" :=
  (fprim_trun f n)
  (at level 67,f at level 0,format "''ftrun' f n") : trm_scope.

Notation "'nthblk f n" :=
  (fprim_nthblk f n)
  (at level 67, f at level 0,format "''nthblk' f n") : trm_scope.

(* ----------Notations of block prim---------------- *)
Notation "'bcreate ln" :=
  (bprim_create ln)
  (at level 67) : trm_scope.

Notation "'bapp b ln" :=
  (bprim_append b ln)
  (at level 67,b at level 0,format "''bapp' b ln") : trm_scope.

Notation "'bsize f" :=
  (bprim_size f)
  (at level 67) : trm_scope.

Notation "'bget b" :=
  (bprim_get b)
  (at level 67) : trm_scope.

Notation "'bsize b" :=
  (bprim_size b)
  (at level 67) : trm_scope.

Notation "'bdelete b" :=
  (bprim_delete b)
  (at level 67) : trm_scope.

Notation "'btrun b n" :=
  (bprim_trun b n)
  (at level 67, b at level 0,format "''btrun' b n") : trm_scope.

(* ----------Notations of aux prim---------------- *)
Notation "n1 '= n2" :=
  (val_eq n1 n2)
  (at level 67) : trm_scope.

Notation "n1 '+ n2" :=
  (val_add n1 n2)
  (at level 67) : trm_scope.

Notation "n1 '- n2" :=
  (val_min n1 n2)
  (at level 67) : trm_scope.

Notation "n1 '<= n2" :=
  (val_le n1 n2)
  (at level 67) : trm_scope.

Notation "ln1 '++ ln2" :=
  (val_list_app ln1 ln2)
  (at level 67) : trm_scope.

Notation "'rev ln1" :=
  (val_list_rev ln1)
  (at level 67) : trm_scope.

Notation "'hd ln1" :=
  (val_list_hd ln1)
  (at level 67) : trm_scope.

Notation "'tl ln1" :=
  (val_list_tl ln1)
  (at level 67) : trm_scope.

Notation "'hdblk ln1" :=
  (val_list_hd_bk ln1)
  (at level 67) : trm_scope.

Notation "'tlblk ln1" :=
  (val_list_tl_bk ln1)
  (at level 67) : trm_scope.

Notation "'len ln1" :=
  (val_list_len ln1)
  (at level 67) : trm_scope.

Notation "'frev lb" :=
  (val_blist_rev lb)
  (at level 67) : trm_scope.

Notation "'buffer b" :=
  (val_new_blist b)
  (at level 67) : trm_scope.

Notation "b 'b+ lb" :=
  (val_blist_buffer b lb)
  (at level 67) : trm_scope.

Notation "'()" := val_unit : trm_scope.

(* ====== Notation for mapreduce ====== *)

(* -- mapper -- *)
Notation "'mapper b" :=
  (bMR_mapper b)
  (at level 67) : trm_scope.

(* -- reducer -- *)
Notation "'merge Lwd" :=
  (fMR_merge Lwd)
  (at level 67) : trm_scope.

Notation "'group lwd" :=
  (fMR_group lwd)
  (at level 67) : trm_scope.

Notation "'reducer Lwd" :=
  (fMR_reducer Lwd)
  (at level 67) : trm_scope.

(*-- some aux list operations --*)
Notation "l 'w:: L" :=
  (val_app_wdlist l L)
  (at level 67, format " l ''w::' L") : trm_scope.

Notation "'reform lwd" :=
  (val_reform lwd)
  (at level 67) : trm_scope.

End NotationForTrm.