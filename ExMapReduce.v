(* ########################### MapReduce ########################### *)
(**

== Representation and verification of WordCount ==

WordCount is a standard MapReduce application.
It counts each word's frequency in a CBS file.

This file shows how we represent the actual application, 
and how we specify and verify the behavior of programs.

Advice: readers need to read Language.v first.

Author: Bowen Zhang.

Date : 2022.11.1
*)

From SLF (* TLC *) Require Export LibCore TLCbuffer.
From SLF (* Sep *) Require Export TripleAndRules ExBasic.
(*------------------------------------------------------------------------*)

Export NotationForTrm.
Export NotationForVariables.

Open Scope val_scope.
Open Scope trm_scope.
Open Scope Z_scope.

(* ########################### WordCount ########################### *)

(*  
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose a HDFS state before WordCount:

--f
  | bk1 [n1;n2]
  | bk2 [n3;n1]
  | bk3 [n2]

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The state after WordCount:

--f
  | bk1 [n1;n2]
  | bk2 [n3;n1]
  | bk3 [n2]

--f2
  | bk4 [n1;2]
  | bk5 [n2;2]
  | bk6 [n3;1]
*)

(* 
------- Representation and Specification ----------

Definition WordCount := 
  Fun 'f :=
    Let 'L1 := Mapper 'f 0 in
    Let 'L2 := Shuffle 'L1 in
    Let 'l := Reducer 'L2 in
    Create_File 'l.


Lemma triple_WordCount: forall Hf Hb (f:floc) (n1 n2 n3 :int) (p1 p2 p3:bloc),
  diff_each_3 n1 n2 n3 ->
  Hf = ( f ~f~> (p1::p2::p3::nil) ) ->
  Hb = ( (p1 ~b~> (n1::n2::nil)) \b* (p2 ~b~> (n3::n1::nil)) \b* (p3 ~b~> (n2::nil)) ) ->
  triple (WordCount f)
    (\R[Hf,Hb])
    (fun r => \exists f1 b4 b5 b6,( \[r= (val_floc f1)] \* 
        (\R[(f1 ~f~> (b4::b5::b6::nil) \f* Hf),
        Hb \b* (b4 ~b~> (n1::2::nil)) \b* (b5 ~b~> (n2::2::nil))
        \b* (b6 ~b~> (n3::1::nil))] ))).

*)


(*------------------------------------------------------------------------*)

(*------------------------------------------------------------------------*)

(* ================================================================= *)
(** Some ltac to simplify the verification *)

(*--- to extract the existential quantifier ---*)
Ltac extexists :=
  intros; simpl; 
  try apply triple_hfexists;
  try apply triple_hfexists';
  try apply triple_hbexists;
  try apply triple_hbexists';
  try apply triple_hexists.

(*--- to extract the pure fact ---*)
Ltac extpure :=
  intros; simpl; 
  try apply triple_hfpure;
  try apply triple_hbpure; 
  try apply triple_hpure;
  simpls;
  intros ->.

(* - combine the extraction - *)
Ltac ext :=
  try extpure; try extexists.

(*--------- Some scripts for CBS-heap entailments --------------*)
Ltac inner_femp :=
 try intros r;
 try rewrite hstar_sep;
 try rewrite hfstar_hempty_l;
 try rewrite hfstar_hempty_r;
 apply himpl_refl.

Ltac inner_bemp :=
 try intros r;
 try rewrite hstar_sep;
 try rewrite hbstar_hempty_l;
 try rewrite hbstar_hempty_r;
 apply himpl_refl.

Ltac outer_emp :=
 try intros r;
 try rewrite hstar_hempty_l';
 try rewrite hstar_hempty_r';
 apply himpl_refl.

Ltac rew_read:=
  intros v;
  rewrite hstar_assoc,hstar_sep,hfstar_hempty_l;
  apply himpl_refl;
  ext.

(*--------- Some scripts for recursive programs --------------*)
Lemma nth_listbloc_1 : forall p1 p2 p3,
(nth_default bnull (to_nat 1) (p1 :: p2 :: p3 :: nil)) = p2.
Proof.
  intros. rewrite to_nat_1,nth_default_succ,nth_default_zero. auto.
Qed.

Lemma nth_listbloc_1' : forall p1 p2,
(nth_default bnull (to_nat 1) (p1 :: p2 :: nil)) = p2.
Proof.
  intros. rewrite to_nat_1,nth_default_succ,nth_default_zero. auto.
Qed.

Lemma nth_listbloc_2 : forall p1 p2 p3,
(nth_default bnull (to_nat (1 + 1)) (p1 :: p2 :: p3 :: nil)) = p3.
Proof.
  intros. rewrite to_nat_plus; try math.
  rewrite to_nat_1. do 2 rewrite nth_default_succ. rewrite~ nth_default_zero.
Qed.

(*----- expand the recursive program  -------*)
Ltac exp_fix :=
  intros; subst; applys* triple_app_fix2; simpl;
  applys triple_let triple_fsize; ext;
  applys triple_let triple_eq; ext;
  applys triple_if; case_if*.

(*----- verify rec body until to the target block -------*)
Ltac fix_body := 
  applys triple_let triple_fget_nth_blk; ext;
  applys triple_let triple_add; ext;
  try rewrite nth_default_zero;
  try rewrite nth_listbloc_1;
  try rewrite nth_listbloc_1';
  try rewrite nth_listbloc_2.

(* ------ for read file example --------- *)
Ltac fix_read :=
  exp_fix; fix_body;
  applys triple_let;
  try applys triple_conseq_frame triple_bget.

(* ------ for map file example --------- *)
Ltac fix_map :=
  exp_fix; fix_body;
  applys triple_let;
  try applys triple_conseq_frame triple_wdmap.


(* ------ for remove file example --------- *)
Ltac fix_rem :=
  exp_fix; fix_body;
  applys triple_seq;
  try applys triple_conseq_frame triple_bdelete.

(* ################################## *)
Lemma eqword_refl : forall n1,
  eqword (n1,1) (n1,1) = true.
Proof. intros. unfold eqword. simpl. apply~ Z.eqb_eq. Qed.

Lemma neqword_refl : forall n1,
  neqword (n1,1) (n1,1) = false.
Proof. intros. unfold neqword. rewrite~ eqword_refl. Qed.

Lemma eqword_diff : forall n1 n2,
  n1 =? n2 = false ->
  eqword (n1,1) (n2,1) = false.
Proof. intros. unfold eqword. simpls~. Qed.

Lemma eqb_comm : forall n1 n2,
  (n1 =? n2) = (n2 =? n1).
Proof.
  intros. destruct (n1 =? n2) eqn:H.
  apply Z.eqb_eq in H. rewrite H.
  symmetry. apply~ Z.eqb_eq.
  symmetry. apply Bool.not_true_is_false.
  intro N.  apply Z.eqb_eq in N.
  rewrite N in H. lets : Z.eqb_eq n1 n1.
  assert (H1: n1 = n1). auto.
  apply H0 in H1. rewrite H in H1. discriminate.
Qed.

Lemma eqword_diff_2 : forall n1 n2,
  n1 =? n2 = false ->
  eqword (n2,1) (n1,1) = false.
Proof. intros. unfold eqword. simpls. rewrite~ eqb_comm. Qed.

Lemma neqword_diff_2 : forall n1 n2,
  n1 =? n2 = false ->
  neqword (n2,1) (n1,1) = true.
Proof. intros. unfold neqword. rewrite~ eqword_diff_2. Qed.

Lemma neqword_diff : forall n1 n2,
  n1 =? n2 = false ->
  neqword (n1,1) (n2,1) = true.
Proof. intros. unfold neqword. rewrite~ eqword_diff. Qed.

Hint Resolve eqword_refl eqword_diff_2 eqb_comm neqword_diff_2 neqword_diff neqword_refl.

Definition diff_each_3 (n1 n2 n3:int) : Prop :=
  n1 =? n2 = false /\ n1 =? n3 = false /\ n2 =? n3 = false.

Lemma diff_3_bool : forall n1 n2 n3,
   diff_each_3 n1 n2 n3 ->
   eqword (n1,1) (n1,1) = true
/\ eqword (n2,1) (n2,1) = true
/\ eqword (n3,1) (n3,1) = true
/\ eqword (n1,1) (n2,1) = false
/\ eqword (n1,1) (n3,1) = false
/\ eqword (n2,1) (n3,1) = false
/\ eqword (n2,1) (n1,1) = false
/\ eqword (n3,1) (n1,1) = false
/\ eqword (n3,1) (n2,1) = false.
Proof. introv. intros (H1&H2&H3). splits*. Qed.

Lemma classify_result: forall n1 n2 n3 lwd,
diff_each_3 n1 n2 n3 ->
lwd = ((n1, 1) :: (n2, 1) :: (n3, 1) :: (n1, 1) :: (n2, 1) :: nil) ->
(classify lwd lwd) = 
( ((n1,1)::(n1,1)::nil) :: ((n2,1)::(n2,1)::nil) :: ((n3,1)::nil) ::
  ((n1,1)::(n1,1)::nil) :: ((n2,1)::(n2,1)::nil) :: nil ) .
Proof.
  intros. apply diff_3_bool in H
  as (H1&H2&H3&H4&H5&H6&H7&H8&H9). subst.
  unfold classify. repeat case_if.
  simpl. repeat case_if. simpl. repeat case_if. simpls~.
Qed.

Lemma diff_3_list_bool : forall n1 n2 n3,
   diff_each_3 n1 n2 n3 ->
   neqlist ((n2, 1) :: (n2, 1) :: nil) ((n3, 1) :: nil) = true
/\ neqlist ((n3, 1) :: nil) ((n1, 1) :: (n1, 1) :: nil) = true
/\ neqlist ((n1, 1) :: (n1, 1) :: nil) ((n3, 1) :: nil) = true
/\ neqlist ((n2, 1) :: (n2, 1) :: nil) ((n1, 1) :: (n1, 1) :: nil) = true
/\ neqlist ((n3, 1) :: nil) ((n2, 1) :: (n2, 1) :: nil) = true
/\ neqlist ((n1, 1) :: (n1, 1) :: nil) ((n1, 1) :: (n1, 1) :: nil) = false
/\ neqlist ((n2, 1) :: (n2, 1) :: nil) ((n2, 1) :: (n2, 1) :: nil) = false
/\ neqlist ((n1, 1) :: (n1, 1) :: nil) ((n2, 1) :: (n2, 1) :: nil) = true.
Proof.
  introv. intros (H1&H2&H3). unfold neqlist, lwdhd.
  repeat rewrite nth_default_zero. splits*.
Qed.

Lemma shuffle_result: forall n1 n2 n3 lwd,
diff_each_3 n1 n2 n3 ->
lwd = ((n1, 1) :: (n2, 1) :: (n3, 1) :: (n1, 1) :: (n2, 1) :: nil) ->
(remove_duplicates (classify lwd lwd)) = 
( ((n1,1)::(n1,1)::nil) :: ((n2,1)::(n2,1)::nil) :: ((n3,1)::nil) ::nil ) .
Proof.
  intros. forwards T : classify_result H H0. rewrite T.
  forwards (H1&H2&H3&H4&H5&H6&H7&H8) : diff_3_list_bool H.
  unfold remove_duplicates. simpl. repeat case_if.
  simpl. repeat case_if. simpl. repeat case_if. simpls~.
Qed.



(*============= Mapper ================*)
Definition Mapper := 
  Fix 'F 'f 'i :=
    Let 'n := 'fsize 'f in
    Let 'be := ('i '= 'n) in
    If_ 'be
    Then (WCval_Listwd nil)
    Else
      Let 'bk := 'nthblk 'f 'i in
      Let 'i1 := 'i '+ 1 in
      Let 'ln := 'mapper 'bk in
      Let 'ln1 := 'F 'f 'i1 in
      'ln 'w:: 'ln1.

(* specification of mapper *)
Lemma triple_Mapper: forall Hf Hb (f:floc) (n1 n2 n3:int) (p1 p2 p3:bloc) (L:(list (list wdpair))),
  diff_each_3 n1 n2 n3 ->
  Hf = ( f ~f~> (p1::p2::p3::nil) ) ->
  Hb = ( (p1 ~b~> (n1::n2::nil)) \b* (p2 ~b~> (n3::n1::nil)) \b* (p3 ~b~> (n2::nil)) ) ->
  L = ( ((n1,1)::(n2,1)::nil) :: ((n3,1)::(n1,1)::nil) :: ((n2,1)::nil) :: nil ) ->
  triple (Mapper f 0)
    (\R[Hf,Hb])
    (fun r => \[r= WCval_Listwd L] \* \R[Hf,Hb]).
Proof.
  fix_map.
  rewrite hstar_sep, hfstar_hempty_l. apply himpl_refl.
  rew_read. ext.

  applys triple_let.
  fix_map.
  rewrite hstar_sep, hfstar_hempty_l,hbstar_comm,hbstar_assoc. apply himpl_refl.
  rew_read. ext.

  applys triple_let.
  fix_map.
  rewrite hstar_sep, hfstar_hempty_l,hbstar_comm,hbstar_assoc. apply himpl_refl.
  rew_read. ext.

  applys triple_let.
  exp_fix.
  applys triple_val'. ext.
  applys triple_app_wdlist. ext.
  applys triple_app_wdlist. ext.
  applys triple_conseq triple_app_wdlist.
  apply himpl_refl.
  intros r. rew_list. 
  rewrite hbstar_comm,hbstar_assoc. apply himpl_refl.
Qed.

(*============= Shuffle ================*)
Definition Shuffle :=
 Fun 'L :=
    Let 'l := 'merge 'L in
      'group 'l.

Lemma triple_Shuffle: forall Hf Hb (n1 n2 n3 : int) (L1 L2: (list (list wdpair))),
  diff_each_3 n1 n2 n3 ->
  L1 = ( ((n1,1)::(n2,1)::nil) :: ((n3,1)::(n1,1)::nil) :: ((n2,1)::nil) :: nil ) ->
  L2 = ( ((n1,1)::(n1,1)::nil) :: ((n2,1)::(n2,1)::nil) :: ((n3,1)::nil) ::nil ) ->
  triple (Shuffle (WCval_Listwd L1))
    (\R[Hf,Hb])
    (fun r => \[r= WCval_Listwd L2] \* \R[Hf,Hb]).
Proof.
  intros. subst.
  applys* triple_app_fun. simpl.
  applys triple_let.
  applys triple_conseq_frame triple_wdmerge.
  rewrite hstar_hempty_r'. applys himpl_refl.
  intros r. rewrite hstar_hempty_r'. simpl. applys himpl_refl.
  ext.
  applys triple_conseq_frame triple_wdgroup.
  rewrite hstar_hempty_r'. applys himpl_refl.
  intros r. rewrite hstar_hempty_r'.
  eapply shuffle_result in H. rewrite <- H.
  applys* himpl_refl. auto.
Qed.

(*============= Reducer ================*)
Definition Reducer :=
  Fun 'L :=  'reducer 'L.

Lemma triple_Reducer: forall Hf Hb (n1 n2 n3 : int) (lwd:list wdpair) (L : (list (list wdpair))),
  diff_each_3 n1 n2 n3 ->
  L = ( ((n1,1)::(n1,1)::nil) :: ((n2,1)::(n2,1)::nil) :: ((n3,1)::nil) ::nil ) ->
  lwd = ((n1,2)::(n2,2)::(n3,1)::nil ) ->
  triple (Reducer (WCval_Listwd L))
    (\R[Hf,Hb])
    (fun r => \[r= WCval_listwdpair lwd] \* \R[Hf,Hb]).
Proof.
  intros. subst.
  applys* triple_app_fun. simpl.
  applys triple_conseq_frame triple_wdreduce.
  rewrite hstar_hempty_r'. applys himpl_refl.
  intros r. rewrite hstar_hempty_r'.
  applys himpl_refl.
Qed.


(*============= Create files ================*)

Lemma triple_CreateBlks' : forall Hf (n1 n2 n3 n4 n5 n6:int),
  triple (CreateBlks (val_listint (n1::n2::n3::n4::n5::n6::nil)) (val_listbloc nil))
    (\R[Hf, \b[] ])
     (fun r => \exists b1 b2 b3,( \[r=(val_listbloc (b3::b2::b1::nil))] \* 
               (\R[Hf, (b1 ~b~> (n1::n2::nil)) \b* (b2 ~b~> (n3::n4::nil) \b* (b3 ~b~> (n5::n6::nil)))]))).
Proof.
  cre_exp_fix. destruct C. auto.
  applys triple_let triple_list_hd_bk. ext.
  applys triple_let triple_list_tl_bk. ext.
  applys triple_let.
  applys triple_conseq_frame triple_bcreate.
  cre_pre. intros r. apply himpl_refl.
  cre_ext. intros b1.
  rewrite hstar_hempty_r. ext.
  applys triple_let triple_blist_buffer. ext.

  exp_fix_create.
  applys triple_conseq_frame triple_bcreate.
  cre_pre. intros r. apply himpl_refl.
  cre_ext. intros b2.
  rewrite hstar_assoc, hstar_sep, hfstar_hempty_r. ext.
  applys triple_let triple_blist_buffer. ext.

  cre_exp_fix. applys triple_let.
  applys triple_conseq_frame triple_bcreate.
  rewrite hstar_sep, hfstar_hempty_r, hbstar_hempty_l. apply himpl_refl.
  intros* r. apply himpl_refl. cre_ext. intros b3.
  rewrite hstar_assoc, hstar_sep, hfstar_hempty_r. ext.
  applys triple_conseq_frame triple_blist_buffer.
  rewrite hstar_hempty_l'. apply himpl_refl.
  intros r. rewrite hstar_hempty_r, hbstar_comm3.
  intros h H. apply hstar_hpure_iff in H as (H1&H2).
  exists b1 b2 b3.
  applys hstar_hpure_iff. splits~.
  destruct C1. rew_list. discriminate.
Qed.

Lemma triple_CreateFile' : forall (n1 n2 n3 n4 n5 n6:int),
  triple (Create_File (val_listint (n1::n2::n3::n4::n5::n6::nil)) )
    (\R[\f[], \b[] ])
     (fun r => \exists f b1 b2 b3,( \[r= (val_floc f)] \* 
               (\R[(f ~f~> (b1::b2::b3::nil)), (b1 ~b~> (n1::n2::nil)) \b* (b2 ~b~> (n3::n4::nil) \b* (b3 ~b~> (n5::n6::nil)))]))).
Proof.
  intros. applys* triple_app_fun.
  applys triple_let triple_CreateBlks'.
  intros v. ext. intros b1. ext. intros b2. ext. intros b3. ext.
  applys triple_let.
  applys triple_conseq_frame triple_blist_rev.
  rewrite hstar_hempty_l'. apply himpl_refl.
  intros r. rewrite hstar_assoc, hstar_hempty_l. apply himpl_refl.
  ext.
  applys triple_conseq_frame triple_fcreate.
  rewrite hstar_hempty_r'. apply himpl_refl.
  intros v. rewrite hstar_hempty_r'.
  apply himpl_hexists_l. intros f.
  intros h M. exists~ f b1 b2 b3.
Qed.

Definition SaveResult : val :=
  Fun 'l:=
    Let 'ln1 := 'reform 'l in
      Create_File 'ln1.

Lemma triple_SaveResult : forall (w1 w2 w3 n1 n2 n3:int),
  triple (SaveResult (WCval_listwdpair ((w1,n1)::(w2,n2)::(w3,n3)::nil)) )
    (\R[\f[], \b[] ])
     (fun r => \exists f b1 b2 b3,( \[r= (val_floc f)] \* 
               (\R[(f ~f~> (b1::b2::b3::nil)), (b1 ~b~> (w1::n1::nil)) \b* (b2 ~b~> (w2::n2::nil) \b* (b3 ~b~> (w3::n3::nil)))]))).
Proof.
  intros. applys* triple_app_fun. simpl.
  applys triple_let triple_MRlist_reform.
  ext. apply triple_CreateFile'.
Qed.



(* $$$$$$$$$$$$$==================$$$$$$$$$$$$$$$$$$$$$ *)


Definition WordCount := 
  Fun 'f :=
    Let 'L := Mapper 'f 0 in
    Let 'L1 := Shuffle 'L in
    Let 'lwd := Reducer 'L1 in
    SaveResult 'lwd.

Lemma triple_WordCount: forall Hf Hb (f:floc) (n1 n2 n3 :int) (p1 p2 p3:bloc),
  diff_each_3 n1 n2 n3 ->
  Hf = ( f ~f~> (p1::p2::p3::nil) ) ->
  Hb = ( (p1 ~b~> (n1::n2::nil)) \b* (p2 ~b~> (n3::n1::nil)) \b* (p3 ~b~> (n2::nil)) ) ->
  triple (WordCount f)
    (\R[Hf,Hb])
    (fun r => \exists f1 b4 b5 b6,( \[r= (val_floc f1)] \* 
        (\R[(f1 ~f~> (b4::b5::b6::nil) \f* Hf),
            (b4 ~b~> (n1::2::nil)) \b* (b5 ~b~> (n2::2::nil))
        \b* (b6 ~b~> (n3::1::nil)) \b* Hb ] ))).
Proof.
  intros. subst.
  applys* triple_app_fun. simpl.
  applys triple_let.
  applys* triple_Mapper.
  simpl. intros r. ext.
  applys triple_let. applys* triple_Shuffle H. ext.
  applys triple_let. applys* triple_Reducer. ext.
  applys triple_conseq_frame triple_SaveResult.
  rewrite hstar_hempty_l'. apply himpl_refl. intros r.
  ext_blk. intros f1. ext_blk. intros b4.
  ext_blk. intros b5. ext_blk. intros b6.
  rewrite hstar_assoc, hstar_sep, hbstar_assoc, hbstar_assoc.
  intros h M. exists~ f1 b4 b5 b6.
Qed.
 
