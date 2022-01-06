(**

This file describes the statements and proof of reasoning rules, mainly about:

  1. the definitions of:
    a. Hoare triple in CBS
    b. Separation Logic triple in CBS (CBS-SL-triple)
  2. how to state and prove the reasoning rules of:
    a. primitive operations (block & file)
    b. terms
    c. structural rules
    (we first state rules by Hoare triple, then prove the SL rules by Hoare rules ).

Author: Bowen Zhang.

Date : 2021.07.24
*)

From SLF (* TLC *) Require Export LibCore TLCbuffer.
From SLF (* CBS *) Require Export Himpl.

(* ################################################################# *)

(*** Implicit Types (to improve the readability) ***)

Implicit Types bp : bloc.
Implicit Types fp : floc.
Implicit Types ln : list int.
Implicit Types n : int.
Implicit Types v : val.
Implicit Types t : trm.
Implicit Types b : bool.
Implicit Types hb : heapb.
Implicit Types sb : stateb.
Implicit Types hf : heapf.
Implicit Types sf : statef.

(*all operators have opaque definitions*)
Global Opaque hbempty hbpure hbstar hbsingle hbexists hbforall.
Global Opaque hfempty hfpure hfstar hfsingle hfexists hfforall.

(* ################################################################# *)
Open Scope liblist_scope.

(* ================================================================= *)
(** ** Hoare reasoning rules ** **)

(**============= * Definition of (total correctness) Hoare triples ================*)

(* -- the behavior of trm in the entire state -- *)
Definition hoare (t:trm) (H:hprop) (Q:val->hprop) :=
forall sf sb, H (sf,sb) -> 
  exists sf' sb' v, eval (sf,sb) t (sf',sb') v /\ Q v (sf',sb').

(** ++++++++++++++++++++  Hoare Reasoning rules  ++++++++++++++++++++ **)

(** ----- block prim operations ------- **)
Lemma hoare_bcreate : forall Hf Hb ll,
  hoare (bval_create (val_listint ll))
    (\R[ Hf, Hb])
    (fun r => \R[ Hf, \existsb bp, \b[r = val_bloc bp] \b* bp ~b~> ll \b* Hb ]).
Proof.
  intros. intros sf sb K0.
  destruct K0 as (P1&P2).
  forwards~ (bp&D&N): (Fmap.single_fresh 0%nat sb ll).
  exists sf ((Fmap.single bp ll) \u sb) (val_bloc bp). subst.
  simpls. splits~.
  (*Notice!!*)
  - applys~ eval_bcreate_sep.
  - splits~. exists bp.
    rewrite <- hbstar_assoc.
    applys~ hbstar_intro.
    rewrite~ hbstar_hpure. splits~.
    applys~ hbsingle_intro.
Qed.

Lemma hoare_bget : forall Hf Hb bp ll,
  hoare (bval_get (val_bloc bp))
    (\R[ Hf, ( (bp ~b~> ll) \b* Hb) ])
    ( fun r => \R[ Hf, ( \b[r = (val_listint ll)] \b* (bp ~b~> ll) \b* Hb)] ).
Proof.
  intros. intros sf sb K0.
  destruct K0 as (P1&P2).
  destruct P2 as (sb1&sb2&D1&D2&D3&D4).
  exists sf sb (val_listint ll). subst.
  splits~.
  - lets (E1&N) : hbsingle_inv D1. subst. simpls.
    applys~ eval_bget_sep. apply D4.
  - splits~. simpls. substs.
    rewrite hbstar_hpure_iff. splits~.
    applys~ hbstar_intro.
Qed.

Lemma hoare_bdelete : forall Hf Hb bp ll,
  hoare (bval_delete (val_bloc bp))
    (\R[ Hf, ( (bp ~b~> ll) \b* Hb) ])
    (fun r => \R[ Hf, ( \b[r = val_unit] \b* Hb) ]).
Proof.
  intros. intros sf sb K0.
  destruct K0 as (P1&P2).
  destruct P2 as (sb1&sb2&D1&D2&D3&D4).
  lets (E1&N): hbsingle_inv D1.
  exists sf sb2 (val_unit). subst.
  splits~.
  - simpls. applys~ eval_bdelete_sep. apply D4.
    apply D3.
  - splits~.
    rewrite~ hbstar_hpure.
Qed.

Lemma hoare_bappend : forall Hf Hb bp l1 l2,
  hoare (bval_append (val_bloc bp) (val_listint l2))
    ( \R[Hf, (bp ~b~> l1) \b* Hb] )
    (fun _ => \R[Hf, (bp ~b~> (l1++l2)) \b* Hb]).
Proof.
  intros. intros sf sb K.
  destruct K as (K1&K2). simpls.
  destruct K2 as (sb1&sb2&D1&D2&D3&D4).
  lets (E1&N): hbsingle_inv D1.
  subst.
  exists sf (single bp (l1++l2) \u sb2) val_unit.
  splits.
  - applys~ eval_bappend_sep.
  - splits~. simpl.
    applys~ hbstar_intro.
      + applys~ hbsingle_intro.
      + applys Fmap.disjoint_single_set D3.
Qed.

Lemma hoare_bsize : forall Hf Hb bp l1,
  hoare (bval_bsize (val_bloc bp) )
    ( \R[Hf, (bp ~b~> l1) \b* Hb] )
    (fun r => \R[Hf, \b[r = List.length l1] \b* (bp ~b~> l1) \b* Hb]).
Proof.
  intros. intros sf sb K.
  destruct K as (K1&K2). simpls.
  destruct K2 as (sb1&sb2&D1&D2&D3&D4).
  exists sf sb (val_int (List.length l1)).
  lets (E1&N): hbsingle_inv D1. subst.
  splits~.
  applys~ eval_bsize_sep.
  splits. simpls~.
  rewrite hbstar_hpure_iff.
  splits~. simpl.
  applys~ hbstar_intro.
Qed.


(** ------------ file prim operations -------------- **)
Lemma hoare_fcreate : forall Hf Hb bll,
  hoare (fval_create (val_listbloc bll))
    (\R[ \f[noduplicates bll] \f* Hf, Hb ])
    (fun r => \R[ (\existsf fp, (\f[r = (val_floc fp)] \f* (fp ~f~> bll) \f* Hf)), Hb]).
Proof.
  intros. intros sf sb K0.
  destruct K0 as (P1&P2).
  destruct P1 as (sf1&sf2&D1&D2&D3&D4).
  forwards~ (fp&D&N) : (Fmap.single_fresh 0%nat sf bll).
  exists (Fmap.single fp bll \u sf) sb (val_floc fp). subst.
  simpls.
  apply hfpure_inv in D1 as [D1 D1'].
  splits~.
  - applys~ eval_fcreate_sep.
  - splits~. exists fp. simpls.
    rewrite <- hfstar_assoc. subst. rewrite union_empty_l.
    applys~ hfstar_intro.
    rewrite~ hfstar_hpure.
    splits~. applys~ hfsingle_intro.
Qed.

Lemma hoare_fget : forall Hf Hb fp bll,
  hoare (fval_get (val_floc fp))
    (\R[ (fp ~f~> bll \f* Hf), Hb])
    (fun r => \R[ ((\f[r = val_listbloc bll]) \f* (fp ~f~> bll) \f* Hf), Hb ]).
Proof.
  intros. intros sf sb K0.
  destruct K0 as (P1&P2).
  destruct P1 as (sf1&sf2&D1&D2&D3&D4).
  exists sf sb (val_listbloc bll). subst. simpls.
  splits~.
  - lets (E1&N) : hfsingle_inv D1. subst.
    applys~ eval_fget_sep.
  - splits~. subst. simpls.
    rewrite hfstar_hpure. splits~.
    applys~ hfstar_intro.
Qed.

Lemma hoare_fget_nth_blk : forall Hf Hb fp bll n,
  hoare (fval_get_nth_blk (val_floc fp) n)
    (\R[ (fp ~f~> bll \f* Hf), Hb ])
    (fun r => \R[ (\f[r = val_bloc (nth_default bnull (Z.to_nat n) bll)] \f* (fp ~f~> bll) \f* Hf),Hb ]).
Proof.
  intros. intros sf sb K.
  destruct K as (P1&P2).
  destruct P1 as (sf1&sf2&D1&D2&D3&D4).
  exists sf sb (val_bloc (nth_default bnull (Z.to_nat n) bll)). subst. simpls.
  splits~.
  - lets (E1&N) : hfsingle_inv D1. subst.
    applys~ eval_fget_nth_blk_sep.
  - splits~. subst. simpls.
    rewrite hfstar_hpure. splits~.
    applys~ hfstar_intro.
Qed.

Lemma hoare_fset_nth_blk : forall Hf Hb fp bll n bp,
  hoare (fval_set_nth_blk (val_floc fp) n (val_bloc bp))
    (\R[ (fp ~f~> bll \f* Hf), Hb ])
    (fun r => \R[ ( (fp ~f~> (LibList.update (to_nat n) bp bll)) \f* Hf), Hb ]).
Proof.
  intros. intros sf sb K.
  destruct K as (P1&P2).
  destruct P1 as (sf1&sf2&D1&D2&D3&D4).
  exists (single fp (LibList.update (to_nat n) bp bll) \u sf2) sb val_unit.
  subst. simpls. lets (E1&N) : hfsingle_inv D1.
  splits~.
  - subst~.
    applys~ eval_fset_nth_blk_sep.
  - splits~.
    applys~ hfstar_intro.
      + applys~ hfsingle_intro.
      + applys Fmap.disjoint_single_set.
        rewrite~ <- E1.
Qed.

Lemma hoare_fdelete : forall Hf Hb fp bll,
  hoare (fval_delete (val_floc fp))
    (\R[ (fp ~f~> bll \f* Hf), Hb ])
    (fun r => \R[ ((\f[r = val_unit]) \f* Hf), Hb ]).
Proof.
  intros. intros sf sb K0.
  destruct K0 as (P1&P2).
  destruct P1 as (sf1&sf2&D1&D2&D3&D4).
  lets (E1&N): hfsingle_inv D1.
  exists sf2 sb val_unit. subst. simpls.
  splits~.
  - applys~ eval_fdelete_sep. apply D4. apply D3.
  - splits~. simpl.
    applys hfstar_hpure_iff. splits~.
Qed.

Lemma hoare_fattach : forall Hf Hb fp bl1 bl2,
  hoare (fval_attach (val_floc fp) (val_listbloc bl2))
    ( \R[(\f[noduplicates bl2] \f* (fp ~f~> bl1) \f* Hf), Hb] )
    (fun _ => \R[(fp ~f~> (bl1++bl2)) \f* Hf, Hb]).
Proof.
  intros. intros sf sb K.
  destruct K as (K1&K2). simpls.
  apply hfstar_hpure_iff in K1 as [K1' K1].
  destruct K1 as (sf1&sf2&D1&D2&D3&D4).
  lets (E1&N): hfsingle_inv D1.
  subst.
  exists (single fp (bl1++bl2) \u sf2) sb val_unit.
  splits.
  - applys~ eval_fattach_sep.
  - splits~. simpl.
    applys~ hfstar_intro.
      + applys~ hfsingle_intro.
      + applys Fmap.disjoint_single_set D3.
Qed.

Lemma hoare_frev_blist : forall Hf Hb bl,
  hoare (fval_rev_blist (val_listbloc bl))
    (\R[Hf, Hb])
    ( fun r => \R[ (\f[r = (val_listbloc (rev bl))] \f* Hf), Hb ] ).
Proof.
  intros. intros sf sb K0.
  destruct K0 as (P1&P2). simpls.
  exists sf sb (val_listbloc (rev bl)). subst.
  splits~. applys eval_frev_blist.
  splits~. applys~ hfstar_hpure_iff.
Qed.

Lemma hoare_fbuffer : forall Hf Hb bp ll,
  hoare (fval_buffer (val_bloc bp))
    (\R[ Hf, ((bp ~b~> ll) \b* Hb) ])
    ( fun r => \R[ ( \f[r = (val_listbloc (bp::nil))] \f* Hf), ((bp ~b~> ll)\b* Hb) ] ).
Proof.
  intros. intros sf sb K0.
  destruct K0 as (P1&P2).
  destruct P2 as (sb1&sb2&D1&D2&D3&D4).
  exists sf sb (val_listbloc (bp::nil)). subst.
  splits~. applys eval_fbuffer.
  splits~. simpls. applys~ hfstar_hpure_iff.
  simpls. subst.
  applys~ hbstar_intro.
Qed.

Lemma hoare_fbuffer_list : forall Hf Hb bp ll bl,
  hoare (fval_buffer_list (val_bloc bp) (val_listbloc bl))
    (\R[ Hf, ((bp ~b~> ll) \b* Hb) ])
    ( fun r => \R[ ( \f[r = (val_listbloc (bp::bl))] \f* Hf), ((bp ~b~> ll)\b* Hb) ] ).
Proof.
  intros. intros sf sb K0.
  destruct K0 as (P1&P2).
  destruct P2 as (sb1&sb2&D1&D2&D3&D4).
  exists sf sb (val_listbloc (bp::bl)). subst.
  splits~. apply eval_fbuffer_list.
  splits~. applys~ hfstar_hpure_iff.
  simpls. subst.
  applys~ hbstar_intro.
Qed.

Lemma hoare_fsize : forall Hf Hb fp lb,
  hoare (fval_fsize (val_floc fp) )
    ( \R[(fp ~f~> lb) \f* Hf, Hb] )
    (fun r => \R[\f[r = List.length lb] \f* (fp ~f~> lb) \f* Hf, Hb]).
Proof.
  intros. intros sf sb K.
  destruct K as (K1&K2). simpls.
  destruct K1 as (sf1&sf2&D1&D2&D3&D4).
  exists sf sb (val_int (List.length lb)).
  lets (E1&N): hfsingle_inv D1. subst.
  splits~. applys~ eval_fsize_sep.
  splits. simpls~.
  rewrite hfstar_hpure_iff.
  splits~. simpl.
  applys~ hfstar_intro. simpls~.
Qed.

(** -------- aux prim operation  ----------- **)
Lemma hoare_add : forall H n1 n2,
  hoare (val_add n1 n2) H
    (fun r => (\[r = (n1+n2)] \* H)).
Proof.
  intros. intros sf sb.
  intros M.
  exists sf sb (n1+n2). splits.
  apply eval_add.
  applys* hstar_hpure_iff.
Qed.

Lemma hoare_eq : forall H n1 n2,
  hoare (val_eq n1 n2) H
    (fun r => (\[r = val_bool (n1 =? n2)] \* H)).
Proof.
  intros. intros sf sb.
  intros M.
  exists sf sb (val_bool (n1 =? n2)). splits.
  apply eval_eq.
  applys* hstar_hpure_iff.
Qed.

Lemma hoare_list_rev : forall H l1,
  hoare (val_list_rev (val_listint l1)) H
    (fun r => (\[r = val_listint (rev l1)] \* H)).
Proof.
  intros. intros sf sb.
  intros M.
  exists sf sb (val_listint (rev l1)). splits.
  apply eval_list_rev.
  applys* hstar_hpure_iff.
Qed.

Lemma hoare_list_app : forall H l1 l2,
  hoare (val_list_app (val_listint l1) (val_listint l2)) H
    (fun r => (\[r = val_listint (l1 ++ l2)] \* H)).
Proof.
  intros. intros sf sb.
  intros M.
  exists sf sb (val_listint (l1 ++ l2)). splits.
  apply eval_list_app.
  applys* hstar_hpure_iff.
Qed.


(** --------- terms  ---------**)
Lemma hoare_eval_like : forall t1 t2 H Q,
  eval_like t1 t2 ->
  hoare t1 H Q ->
  hoare t2 H Q.
Proof.
  introv E M1 K0. forwards (sf'&sb'&v&R1&K1) : M1 K0.
  exists sf' sb' v. splits~.
Qed.

Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof.
  introv M. intros hf hb k.
  exists hf hb v. splits~.
  applys eval_val.
Qed.

Lemma hoare_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  hoare (trm_fun x t1) H Q.
Proof.
  introv M. intros hf hb k. exists hf hb __.
  splits~. applys eval_fun.
Qed.

Lemma hoare_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  hoare (trm_fix f x t1) H Q.
Proof.
  introv M. intros hf hb k. exists hf hb __.
  splits~. apply eval_fix.
Qed.

Lemma hoare_app_fun: forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  hoare (subst x v2 t1) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof.
  introv E M. intros sf sb K0.
  forwards (sf'&sb'&v&R1&K1) : (rm M) K0.
  exists sf' sb' v.
  splits~. applys eval_app_fun E R1.
Qed.

Lemma hoare_app_fix:forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  hoare (subst x v2 (subst f v1 t1)) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof.
  introv E M. intros sf sb K0. forwards (sf'&sb'&v&R1&K1): (rm M) K0.
  exists sf' sb' v. splits. { applys eval_app_fix E R1. } { applys K1. }
Qed.

Lemma hoare_seq : forall t1 t2 H Q H1,
  hoare t1 H (fun r => H1) ->
  hoare t2 H1 Q ->
  hoare (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (hf1&hb1&v1&R1&K1): (rm M1).
  forwards* (hf2&hb2&v2&R2&K2): (rm M2).
  exists hf2 hb2 v2. splits~. { applys~ eval_seq R1 R2. }
Qed.

Lemma hoare_let : forall x t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall v, hoare (subst x v t2) (Q1 v) Q) ->
  hoare (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (hf1&hb1&v1&R1&K1): (rm M1).
  forwards* (hf2&hb2&v2&R2&K2): (rm M2).
  exists hf2 hb2 v2. splits~. { applys~ eval_let R2. }
Qed.

Lemma hoare_if : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros hf hb Hh. forwards* (hf1&hb1&v1&R1&K1): (rm M1).
  exists hf1 hb1 v1. splits~. { applys* eval_if. }
Qed.

(*----- structural rules ------*)
Lemma hoare_conseq : forall t H' Q' H Q,
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using.
  introv M MH MQ HF. forwards (sf'&sb'&v&R&K): M sf sb. { applys~ himpl_inv. }
  exists sf' sb' v. splits~. { applys~ himpl_inv. }
Qed.

(* ================================================================================ *)
(** ** Separation Logic reasoning rules ** **)
Open Scope Z_scope.
(**============= * Definition of Separation Logic triple ================*)
Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
forall Hf Hb,
    hoare t (H \* \R[Hf,Hb]) (Q \*+ \R[Hf,Hb]).


(* ------------ SL structural rules ----------------- *)

(*  _______________Frame Rule in CBS__________________  *)
Lemma triple_frame : forall t H Q Hf Hb,
  triple t H Q ->
  triple t (H \* (\R[Hf,Hb])) (Q \*+ (\R[Hf,Hb])).
Proof.
  unfold triple, hoare. introv M.
  intros Hf' Hb' sf sb.
  specializes M (Hf \f* Hf') (Hb \b* Hb').
  introv N.
  rewrite hstar_assoc, hstar_sep in N.
  apply M in N as (sf'&sb'&v&N1&N2).
  exists sf' sb' v.
  rewrite hstar_assoc, hstar_sep.
  splits~.
Qed.

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof.
  introv M N R.
  unfolds triple.
  intros Hf Hb. specializes M Hf Hb.
  applys hoare_conseq.
  applys M. applys~ himpl_frame_l.
  intros v. applys~ himpl_frame_l.
Qed.

Lemma triple_conseq_frame : forall H Q Hf Hb H1 Q1 t ,
  triple t H1 Q1 ->
  H ==> H1 \* (\R[Hf, Hb]) ->
  Q1 \*+ (\R[Hf, Hb]) ===> Q ->
  triple t H Q.
Proof.
  introv M N R.
  unfolds triple.
  intros Hf' Hb'.
  specializes M (Hf \f* Hf') (Hb \b* Hb').
  applys hoare_conseq. applys M.
  rewrite <- hstar_sep, <- hstar_assoc;
  applys~ himpl_frame_l.
  intros v. rewrite <- hstar_sep. rewrite <- hstar_assoc.
  applys~ himpl_frame_l.
Qed.

(*---------- extract the prue fact and quantifier from precondition ----------*)
Lemma triple_hpure : forall t (P:Prop) Hf Hb Q,
  (P -> triple t (\R[Hf,Hb]) Q) ->
  triple t (\[P] \* \R[Hf,Hb]) Q.
Proof.
  unfold triple. intros. rewrite hstar_assoc,hstar_sep.
  intros hf hb M. apply hstar_hpure_iff in M as [MA MB].
  applys~ H. rewrite~ hstar_sep.
Qed.

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall (x:A), triple t (J x) Q) ->
  triple t (\exists (x:A), J x) Q.
Proof.
  unfold triple. intros.
  intros hf hb M.
  rewrite hstar_hexists in M.
  destruct M as (v&M).
  specializes H v.
  applys~ H.
Qed.

Lemma triple_hbpure : forall t (P:Prop) Hf Hb Q,
  (P -> triple t (\R[Hf,Hb]) Q) ->
  triple t (\R[Hf,\b[P] \b* Hb]) Q.
Proof.
  unfold triple.
  intros. intros hf hb. rewrite hstar_sep.
  intros (MA&MB). simpls.
  rewrite hbstar_assoc in MB.
  apply hbstar_hpure_iff in MB as [MB1 MB2].
  eapply H in MB1. apply MB1.
  rewrite hstar_sep. splits~.
Qed.

Lemma triple_hfpure : forall t (P:Prop) Hf Hb Q,
  (P -> triple t (\R[Hf,Hb]) Q) ->
  triple t (\R[\f[P] \f* Hf,Hb]) Q.
Proof.
  unfold triple.
  intros. intros hf hb. rewrite hstar_sep.
  intros (MA&MB). simpls.
  rewrite hfstar_assoc in MA.
  apply hfstar_hpure_iff in MA as [MA1 MA2].
  eapply H in MA1. apply MA1.
  rewrite hstar_sep. splits~.
Qed.

Lemma triple_hbpure' : forall t (P:Prop) Hf Q,
  (P -> triple t (\R[Hf,\b[]]) Q) ->
  triple t (\R[Hf,\b[P]]) Q.
Proof.
  intros. lets M : triple_hbpure \b[].
  rewrite~ hbstar_hempty_r in M.
Qed.

Lemma triple_hfpure' : forall t (P:Prop) Hb Q,
  (P -> triple t (\R[\f[],Hb]) Q) ->
  triple t (\R[\f[P],Hb]) Q.
Proof.
  intros. lets M : triple_hfpure \f[].
  rewrite~ hfstar_hempty_r in M.
Qed.

Lemma triple_hbexists : forall t (A:Type) (J:A->hbprop) Hf Hb Q,
  (forall (x:A), triple t (\R[ Hf, (J x) \b* Hb]) Q) ->
  triple t (\R[ Hf, (\existsb (x:A), J x) \b* Hb]) Q.
Proof.
  unfold triple. intros. rewrite hstar_sep, hbstar_assoc.
  intros hf hb (MA&MB). simpls.
  rewrite hbstar_hexists in MB.
  destruct MB as (v&MB).
  specializes H v. apply H.
  rewrite hstar_sep. splits~. rewrite~ hbstar_assoc.
Qed.

Lemma triple_hbexists' : forall t (A:Type) (J:A->hbprop) Hf Q,
  (forall (x:A), triple t (\R[ Hf, (J x)]) Q) ->
  triple t (\R[ Hf, (\existsb (x:A), J x)]) Q.
Proof.
  intros. lets M : triple_hbexists \b[].
  rewrite~ hbstar_hempty_r in M. apply M.
  intros. rewrite~ hbstar_hempty_r.
Qed.

Lemma triple_hfexists : forall t (A:Type) (J:A->hfprop) Hf Hb Q,
  (forall (x:A), triple t (\R[(J x)\f*Hf, Hb]) Q) ->
  triple t (\R[ (\existsf (x:A), J x) \f*Hf, Hb]) Q.
Proof.
  unfold triple. intros. rewrite hstar_sep, hfstar_assoc.
  intros hf hb (MA&MB). simpls.
  rewrite hfstar_hexists in MA.
  destruct MA as (v&MA).
  specializes H v. apply H.
  rewrite hstar_sep. splits~. rewrite~ hfstar_assoc.
Qed.

Lemma triple_hfexists' : forall t (A:Type) (J:A->hfprop) Hb Q,
  (forall (x:A), triple t (\R[ (J x), Hb]) Q) ->
  triple t (\R[ (\existsf (x:A), J x), Hb]) Q.
Proof.
  intros. lets M : triple_hfexists \f[].
  rewrite~ hfstar_hempty_r in M. apply M.
  intros. rewrite~ hfstar_hempty_r.
Qed.


(*++++++++++++++++++ 新加的引理 +++++++++++++++++++++*)
Parameter hexists_intro : forall {A} (x:A) (J:A->hprop) h,
  J x h ->
  (hexists J) h.

(*========================== 最弱前置条件语义 ==============================*)
Definition wp (t:trm) (Q:val->hprop) : hprop :=
  \exists (Hf:hfprop) (Hb:hbprop), \R[Hf,Hb] \* \[triple t (\R[Hf,Hb]) Q].

Lemma wp_pre : forall t Q,
  triple t (wp t Q) Q.
Proof.
  intros. unfold wp.
  apply triple_hexists.
  intros Hf.
  apply triple_hexists.
  intros Hb.
  rewrite hstar_comm.
  applys~ triple_hpure.
Qed.

Lemma wp_weakest : forall t Hf Hb Q,
  triple t (\R[Hf,Hb]) Q ->
  \R[Hf,Hb] ==> wp t Q.
Proof.
  introv N. unfold wp.
  hnf. introv M.
  apply (hexists_intro Hf).
  apply (hexists_intro Hb).
  rewrite hstar_comm,hstar_hpure_iff.
  split~.
Qed.

Lemma wp_equiv : forall t Hf Hb Q,
  (\R[Hf,Hb] ==> wp t Q) <-> (triple t (\R[Hf,Hb]) Q).
Proof using.
  iff M.
  - applys triple_conseq.
    applys wp_pre; auto.
    apply M. intro h. apply himpl_refl.
  - apply~ wp_weakest.
Qed.
























(**====================  separation logic rule  ===========================**)

(*------------------ SL rule: block prim operations---------------*)
Lemma triple_bcreate : forall Hf ll,
  triple (bval_create (val_listint ll))
    (\R[ Hf, \b[] ])
    (fun r => (\R[ Hf, (\existsb bp, \b[r= (val_bloc bp)] \b* bp ~b~> ll)]) ).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_bcreate hstar_sep_l.

  intros r h M.
  destruct M as (MA&MB).
  rewrite hstar_sep, state_get_eq.
  splits~. simpls.
  destruct MB as (pb&MB).
  rewrite hbstar_hexists. exists pb.
  apply hbstar_hpure_iff in MB as [MB1 MB].
  rewrite hbstar_comm, hbstar_assoc, hbstar_hempty_l in MB.
  rewrite~ hbstar_assoc. rewrite hbstar_hpure_iff.
  splits~. rewrite~ hbstar_comm.
Qed.

Lemma triple_bget: forall Hf bp ll,
  triple (bval_get bp)
    (\R[ Hf, (bp ~b~> ll)])
    (fun r =>(\R[ Hf, (\b[r=(val_listint ll)] \b* (bp ~b~> ll))])).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_bget hstar_sep_l.
  intros r h R.
  destruct R as (HA&HB).
  rewrite hstar_sep, state_get_eq.
  splits~. simpl.
  rewrite~ hbstar_assoc.
Qed.

Lemma triple_bdelete: forall Hf bp ll,
  triple (bval_delete bp)
    (\R[ Hf, (bp ~b~> ll)])
    (fun _ =>(\R[ Hf, \b[]])).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_bdelete hstar_sep_l.
  intros r h R.
  destruct R as (HA&HB).
  rewrite hstar_sep, state_get_eq.
  splits~. simpls.
  apply hbstar_hpure_iff in HB as [HB HB'].
  rewrite~ hbstar_hempty_l.
Qed.

Lemma triple_bappend : forall Hf bp l1 l2,
  triple (bval_append bp (val_listint l2))
    ( \R[Hf, (bp ~b~> l1)] )
    (fun _ => \R[Hf, bp ~b~> (l1++l2)]).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_bappend.
  rewrite hstar_sep. apply himpl_refl.
  intros r h (RA&RB).
  rewrite hstar_sep, state_get_eq.
  splits~.
Qed.

Lemma triple_bsize : forall Hf bp l1,
  triple (bval_bsize bp )
    ( \R[Hf, (bp ~b~> l1)] )
    (fun r => \R[Hf, \b[r = List.length l1] \b* (bp ~b~> l1)]).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_bsize.
  rewrite hstar_sep. apply himpl_refl.
  intros r h (RA&RB).
  rewrite hstar_sep, state_get_eq, hbstar_assoc.
  splits~.
Qed.

(*-------------------- SL rule: file prim operations -------------------*)
Lemma triple_fcreate : forall Hb bll,
  triple (fval_create (val_listbloc bll))
    (\R[ \f[noduplicates bll], Hb ])
    (fun r => \R[ (\existsf fp, (\f[r = val_floc fp] \f* (fp ~f~> bll))), Hb ]).
Proof.
  intros. intros Hf' Hb'.
  applys hoare_conseq hoare_fcreate hstar_sep_l.
  introv M.
  destruct M as (M1&M2).
  destruct M1 as (fp&M1).
  rewrite hstar_sep, state_get_eq.
  splits~. simpls.
  rewrite hfstar_hexists. exists fp.
  rewrite~ hfstar_assoc.
Qed.

Lemma triple_fget: forall Hb fp bll,
  triple (fval_get fp)
    (\R[ (fp ~f~> bll), Hb])
    (fun r =>(\R[ (\f[r=(val_listbloc bll)] \f* (fp ~f~> bll)), Hb])).
Proof.
  intros. intros Hf' Hb'.
  applys hoare_conseq hoare_fget hstar_sep_l.
  intros r h M.
  destruct M as (M1&M2).
  rewrite hstar_sep, state_get_eq.
  splits~. simpl.
  rewrite~ hfstar_assoc.
Qed.

Lemma triple_fget_nth_blk : forall Hb fp bll n,
  triple (fval_get_nth_blk fp n)
    (\R[ fp ~f~> bll, Hb ])
    (fun r => \R[ (\f[r = val_bloc (nth_default bnull (Z.to_nat n) bll)] \f* (fp ~f~> bll)),
                   Hb ]).
Proof.
  intros. intros Hf' Hb'.
  applys hoare_conseq hoare_fget_nth_blk hstar_sep_l.
  intros r h M.
  destruct M as (M1&M2).
  rewrite hstar_sep, state_get_eq.
  splits~. simpl.
  rewrite~ hfstar_assoc.
Qed.

Lemma triple_fset_nth_blk : forall Hb fp bll n bp,
  triple (fval_set_nth_blk fp n bp)
    (\R[ fp ~f~> bll, Hb ])
    (fun r => \R[ (fp ~f~> (LibList.update (Z.to_nat n) bp bll)), Hb ]).
Proof.
  intros. intros Hf' Hb'.
  applys hoare_conseq hoare_fset_nth_blk hstar_sep_l.
  intros r h M.
  destruct M as (M1&M2).
  rewrite hstar_sep, state_get_eq.
  splits~.
Qed.

Lemma triple_fdelete: forall Hb fp bll,
  triple (fval_delete fp)
    (\R[ (fp ~f~> bll), Hb])
    (fun r =>(\R[ \f[], Hb])).
Proof.
  intros. intros Hf' Hb'.
  applys hoare_conseq hoare_fdelete hstar_sep_l.
  intros r h M.
  destruct M as (M1&M2).
  rewrite hstar_sep, state_get_eq.
  splits~. simpl.
  apply hfstar_hpure_iff in M1 as [M1 M1'].
  rewrite~ hfstar_hempty_l.
Qed.

Lemma triple_fattach: forall Hb fp bl1 bl2,
  triple (fval_attach fp (val_listbloc bl2))
    ( \R[(\f[noduplicates bl2] \f* (fp ~f~> bl1)), Hb] )
    (fun r =>(\R[(fp ~f~> (bl1++bl2)), Hb])).
Proof.
  intros. intros Hf' Hb'.
  applys hoare_conseq hoare_fattach.
  rewrite hstar_sep, hfstar_assoc.
  apply himpl_refl.
  intros r. rewrite hstar_sep. apply himpl_refl.
Qed.

Lemma triple_fsize : forall Hb fp lb,
  triple (fval_fsize fp )
    ( \R[(fp ~f~> lb), Hb] )
    (fun r => \R[\f[r = List.length lb] \f* (fp ~f~> lb), Hb]).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_fsize.
  rewrite hstar_sep. apply himpl_refl.
  intros r h (RA&RB).
  rewrite hstar_sep, state_get_eq, hfstar_assoc.
  splits~.
Qed.

Lemma triple_frev_blist : forall H bl,
  triple (fval_rev_blist (val_listbloc bl))
    H
    ( fun r => \[r = (val_listbloc (rev bl))] \* H ).
Proof.
  intros. intros Hf Hb sf sb M.
  exists sf sb (val_listbloc (rev bl)). splits.
  apply eval_frev_blist. rewrite hstar_assoc.
  applys* hstar_hpure_iff.
Qed.

Lemma triple_fbuffer : forall bp H,
  triple (fval_buffer bp)
    H
    (fun r => \[r= val_listbloc (bp::nil)] \* H ).
Proof.
  intros. intros Hf Hb sf sb M.
  exists sf sb (val_listbloc (bp::nil)). splits.
  apply eval_fbuffer. rewrite hstar_assoc.
  applys* hstar_hpure_iff.
Qed.

Lemma triple_fbuffer_list : forall bp bl H,
  triple (fval_buffer_list bp (val_listbloc bl))
    H
    ( fun r => \[r = (val_listbloc (bp::bl))] \* H ).
Proof.
  intros. intros Hf Hb sf sb M.
  exists sf sb (val_listbloc (bp::bl)). splits.
  apply eval_fbuffer_list. rewrite hstar_assoc.
  applys* hstar_hpure_iff.
Qed.


(* -------------------- SL rule: aux prim operations------------------ *)

Lemma triple_add : forall H n1 n2,
  triple (val_add n1 n2) H
    (fun r => (\[r = (n1 + n2)] \* H)).
Proof.
  intros. unfold triple. intros Hf Hb sf sb M.
  exists sf sb (n1+n2).
  splits~. apply eval_add.
  rewrite hstar_assoc.
  apply* hstar_hpure_iff.
Qed.

Lemma triple_eq : forall H n1 n2,
  triple (val_eq n1 n2) H
    (fun r => (\[r = val_bool (n1 =? n2)] \* H)).
Proof.
  intros. unfold triple. intros Hf Hb sf sb M.
  exists sf sb (val_bool (n1 =? n2)).
  splits~. apply eval_eq.
  rewrite hstar_assoc.
  apply* hstar_hpure_iff.
Qed.

Lemma triple_list_rev : forall H l1,
  triple (val_list_rev (val_listint l1)) H
    (fun r => (\[r = val_listint (rev l1)] \* H)).
Proof.
  intros. unfold triple. intros Hf Hb sf sb M.
  exists sf sb (val_listint (rev l1)).
  splits~. apply eval_list_rev.
  rewrite hstar_assoc.
  apply* hstar_hpure_iff.
Qed.

Lemma triple_list_app : forall H l1 l2,
  triple (val_list_app (val_listint l1) (val_listint l2)) H
    (fun r => (\[r = val_listint (l1 ++ l2)] \* H)).
Proof.
  intros. intros Hf Hb sf sb M.
  exists sf sb (val_listint (l1 ++ l2)). splits.
  apply eval_list_app. rewrite hstar_assoc.
  applys* hstar_hpure_iff.
Qed.


(* ----------------  SL rule: terms   --------------- *)
Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof.
  introv M. unfold triple. intros. applys hoare_val.
  applys~ himpl_frame_l.
Qed.

Lemma triple_val' : forall v H,
  triple (trm_val v) H (fun r => \[r = v] \* H).
Proof.
  introv M. unfold triple. intros.
  exists sf sb v. splits~. apply eval_val.
  rewrite hstar_assoc, hstar_hpure_iff.
  splits~.
Qed.

Lemma triple_fix: forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.
Proof.
  unfold triple. introv M.
  intros Hf' Hb'.
  applys hoare_fix.
  applys~ himpl_frame_l.
Qed.

Lemma triple_eval_like : forall t1 t2 H Q,
  eval_like t1 t2 ->
  triple t1 H Q ->
  triple t2 H Q.
Proof using.
  introv E M1. intros Hf Hb. applys hoare_eval_like E. applys M1.
Qed.

Lemma triple_trm_equiv : forall t1 t2 H Q,
  trm_equiv t1 t2 ->
  triple t1 H Q <-> triple t2 H Q.
Proof using.
  introv E. unfolds trm_equiv. iff M.
  { applys triple_eval_like M. introv R. applys* E. }
  { applys triple_eval_like M. introv R. applys* E. }
Qed.

Lemma triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.
Proof.
  introv M.
  unfold triple. intros Hf Hb.
  applys hoare_fun. applys~ himpl_frame_l.
Qed.

Lemma triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.
Proof.
  introv M N.
  applys triple_eval_like N.
  introv R. applys eval_app_fun M R.
Qed.

Lemma triple_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  triple (subst x v2 (subst f v1 t1)) H Q ->
  triple (trm_app v1 v2) H Q.
Proof.
  introv M N.
  applys triple_eval_like N.
  introv R. applys eval_app_fix M R.
Qed.

Lemma triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof.
  introv M1 M2. intros Hf Hb.
  applys~ hoare_seq.
Qed.

Lemma triple_let :forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall v, triple (subst x v t2) (Q1 v) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof.
  introv M1 M2. intros Hf Hb.
  applys~ hoare_let. intros. apply M2.
Qed.

Lemma triple_if : forall b t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if (val_bool b) t1 t2) H Q.
Proof.
  unfold triple.
  introv M. intros Hf Hb.
  applys hoare_if M.
Qed.






(*====================== Optimization for Multi arguments =========================*)

(*--- two arguments ---*)
Lemma eval_like_app_fun2 : forall v0 v1 v2 x1 x2 t1,
  v0 = val_fun x1 (trm_fun x2 t1) ->
  (x1 <> x2) ->
  eval_like (subst x2 v2 (subst x1 v1 t1)) (v0 v1 v2).
Proof using.
  introv E N. introv R.
  applys~ eval_app_args.
  - applys~ eval_app_fun E. simpl.
    rewrite var_eq_spec. case_if.
    applys eval_fun.
  - applys eval_val.
  - applys* eval_app_fun.
Qed.

Lemma eval_like_app_fix2 : forall f v0 v1 v2 x1 x2 t1,
  v0 = val_fix f x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ f <> x2) ->
  eval_like (subst x2 v2 (subst x1 v1 (subst f v0 t1))) (v0 v1 v2).
Proof using.
  introv E (N1&N2). introv R.
  applys~ eval_app_args.
  - applys~ eval_app_fix E. simpl.
    do 2 (rewrite var_eq_spec; case_if).
    applys eval_fun.
  - applys eval_val.
  - applys* eval_app_fun.
Qed.

Lemma triple_app_fun2 : forall x1 x2 v0 v1 v2 t1 H Q,
  v0 = val_fun x1 (trm_fun x2 t1) ->
  (x1 <> x2) ->
  triple (subst x2 v2 (subst x1 v1 t1)) H Q ->
  triple (v0 v1 v2) H Q.
Proof using.
  introv E N M1. applys triple_eval_like M1. applys* eval_like_app_fun2.
Qed.

Lemma triple_app_fix2 : forall f x1 x2 v0 v1 v2 t1 H Q,
  v0 = val_fix f x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ f <> x2) ->
  triple (subst x2 v2 (subst x1 v1 (subst f v0 t1))) H Q ->
  triple (v0 v1 v2) H Q.
Proof using.
  introv E N M1. applys triple_eval_like M1. applys* eval_like_app_fix2.
Qed.

(* --- three args --- *)

Lemma eval_like_app_fun3 : forall v0 v1 v2 v3 x1 x2 x3 t1,
  v0 = val_fun x1 (trm_fun x2 (trm_fun x3 t1)) ->
  (x1 <> x2  /\ x1 <> x3 /\ x2 <> x3) ->
  eval_like (subst x3 v3 (subst x2 v2 (subst x1 v1 t1))) (v0 v1 v2 v3).
Proof.
  introv E (N1&N2&N3). introv R. applys* eval_app_args.
  { applys* eval_like_app_fun2 E. simpl. do 2 (rewrite var_eq_spec; case_if). applys eval_fun. }
  { applys eval_val. }
  { applys* eval_app_fun. }
Qed.

Lemma triple_app_fun3 : forall x1 x2 x3 v0 v1 v2 v3 t1 H Q,
  v0 = val_fun x1 (trm_fun x2 (trm_fun x3 t1)) ->
  (x1 <> x2  /\ x1 <> x3 /\ x2 <> x3) ->
  triple (subst x3 v3 (subst x2 v2 (subst x1 v1 t1))) H Q ->
  triple (v0 v1 v2 v3) H Q.
Proof.
  introv E (N1&N2&N3) M.
  applys triple_eval_like M. applys* eval_like_app_fun3.
Qed.
