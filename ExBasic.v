(**

This file describes the representation and verification of 
some CBS Basic data operations.

Examples are mainly about:
  1. copy a block
  2. remove a file(rec)
  3. read a file (rec)
  4. create files
  5. copy a file

Notice: readers should read Language.v first.

Author: Bowen Zhang.

Date : 2022.01.06
*)

From SLF (* TLC *) Require Export LibCore TLCbuffer.
From SLF (* Sep *) Require Export Rules.

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
  try rewrite nth_listbloc_2.

(* ------ for read file example --------- *)
Ltac fix_read :=
  exp_fix; fix_body;
  applys triple_let;
  try applys triple_conseq_frame triple_bget.

(* ------ for remove file example --------- *)
Ltac fix_rem :=
  exp_fix; fix_body;
  applys triple_seq;
  try applys triple_conseq_frame triple_bdelete.

(*------------------------------------------------------------------------*)

(* ###########################  Examples #################################*)

(* !! Need to read the Language.v firstly !! *)
Export NotationForTrm.
Export NotationForVariables.

Open Scope val_scope.
Open Scope trm_scope.
Open Scope Z_scope.

(*========================= Copy a block ================================*)
(*
val_fun bk 
  (trm_let ln (trm_app (trm_val (val_bval bval_get)) (trm_var bk))
	  trm_app (trm_val (val_bval bval_create)) (trm_var ln))
*)

Definition Copy_blk : val := 
  Fun 'bk :=
    Let 'ln := 'bget 'bk in
    'bcreate 'ln.


Lemma triple_Copy_blk : forall Hf (bp:bloc) (l:listint),
  triple (Copy_blk bp)
    (\R[Hf, bp ~b~> l] )
    (fun r => \exists bp',\[r=(val_bloc bp')] \* (\R[Hf,(bp' ~b~> l) \b* (bp ~b~> l)])).
Proof.
  intros. applys* triple_app_fun.
  applys triple_let triple_bget. ext.
  applys triple_conseq_frame triple_bcreate.
  rewrite* hstar_hempty_l'.
  introv M. rewrite hstar_hexists in M.
  destruct M as (bp'&M).
  rewrite hstar_assoc, hstar_sep, hfstar_hempty_l in M.
  exists~ bp'.
Qed.

(*========================= Remove a file (rec) ================================*)
(*   --pseudo code--
  Fix F f i :=
    let n = sizeof f in
    if (i = n) then
      fdelete f
    else
      let b = f.i in
      let i = i + 1 in
      bdelete b ;
      F f i.
*)

Definition Remove_f := 
  Fix 'F 'f 'i :=
    Let 'n := 'fsize 'f in
    Let 'be := ('i '= 'n) in
    If_ 'be
    Then ('fdelete 'f)
    Else
      Let 'bk := 'nth_blk 'f 'i in
      Let 'i1 := 'i '+ 1 in
      'bdelete 'bk ';
      'F 'f 'i1.

Lemma triple_Remove_f:  forall Hf Hb (f:floc) (p1 p2 p3 p4:bloc) (l1 l2 l3 l4:listint),
  Hf = ( f ~f~> (p1::p2::p3::p4::nil) ) ->
  Hb = ( (p1 ~b~> l1) \b* (p2 ~b~> l2) \b* (p3 ~b~> l3) \b* (p4 ~b~> l4) ) ->
  triple (Remove_f f 0)
    (\R[Hf,Hb])
    (fun _ =>  \R[\f[],\b[]]).
Proof.
  fix_rem. inner_femp. outer_emp. (*1st time*)
  fix_rem. inner_femp. outer_emp. (*2nd time*)
  fix_rem. inner_femp. outer_emp. (*2nd time*)
  fix_rem. outer_emp. outer_emp.  (*3rd time*)
  exp_fix. applys triple_fdelete. (*end rec*)
Qed.


(*========================= Read a file (rec) ================================*)
Definition Read_f := 
  Fix 'F 'f 'i :=
    Let 'n := 'fsize 'f in
    Let 'be := ('i '= 'n) in
    If_ 'be
    Then (val_listint nil)
    Else
      Let 'bk := 'nth_blk 'f 'i in
      Let 'i1 := 'i '+ 1 in
      Let 'ln := 'bget 'bk in
      Let 'ln1 := 'F 'f 'i1 in
      'ln '++ 'ln1.

Lemma triple_Read_f: forall Hf Hb (f:floc) (p1 p2 p3:bloc) (n1 n2 n3 n4 n5:int),
  Hf = ( f ~f~> (p1::p2::p3::nil) ) ->
  Hb = ( (p1 ~b~> (n1::n2::nil)) \b* (p2 ~b~> (n3::n4::nil)) \b* (p3 ~b~> (n5::nil)) ) ->
  triple (Read_f f 0)
    (\R[Hf,Hb])
    (fun r => \[r= val_listint (n1::n2::n3::n4::n5::nil)] \* \R[Hf,Hb]).
Proof.
  fix_read.
  rewrite hstar_sep, hfstar_hempty_l. apply himpl_refl.
  rew_read. ext.

  applys triple_let.
  fix_read.
  rewrite hstar_sep, hfstar_hempty_l,hbstar_comm,hbstar_assoc. apply himpl_refl.
  rew_read. ext.

  applys triple_let.
  fix_read.
  rewrite hstar_sep, hfstar_hempty_l,hbstar_comm,hbstar_assoc. apply himpl_refl.
  rew_read. ext.

  applys triple_let.
  exp_fix.
  applys triple_val'. ext.
  applys triple_list_app. ext.
  applys triple_list_app. ext.
  applys triple_conseq triple_list_app.
  apply himpl_refl.
  intros r. rew_list. 
  rewrite hbstar_comm,hbstar_assoc. apply himpl_refl.
Qed.

(*===================== Create files ===========================*)

(*-------- create a file with two blocks -----------*)
Definition Create_blk2 : val :=
  Fun 'ln1 'ln2 :=
    Let 'bk1 := 'bcreate 'ln1 in
    Let 'bk2 := 'bcreate 'ln2 in
    Let 'lb := 'fbuffer 'bk2 in
    'bk1 'b+ 'lb.

Lemma triple_Create_blk2 : forall Hf (l1 l2:listint),
  triple (Create_blk2 (val_listint l1) (val_listint l2))
    (\R[Hf, \b[] ])
     (fun r => \exists bp1 bp2,( \[r=(val_listbloc (bp1::bp2::nil))] \* 
               (\R[Hf, (bp1 ~b~> l1) \b* (bp2 ~b~> l2)]))).
Proof.
  intros. applys triple_app_fun2. reflexivity. auto.
  simpl. applys triple_let triple_bcreate'.
  ext. intros b1. ext.

  applys triple_let.
  applys triple_conseq_frame triple_bcreate'.
  rewrite hstar_hempty_l'. apply himpl_refl.
  intros v. inner_femp.
  ext. intros b2. rewrite hbstar_assoc. ext.
  applys triple_let triple_fbuffer. ext.
  applys triple_conseq_frame triple_fbuffer_list.
  outer_emp.
  { intros r h. rewrite hstar_hempty_r', hstar_hpure, hbstar_comm.
    intros (MA&MB). exists~ b1 b2. rewrite hstar_hpure. splits~. }
Qed.

Definition Newf_blk2 :val := 
  Fun 'ln1 'ln2 :=
    Let 'lb := Create_blk2 'ln1 'ln2 in
    'fcreate 'lb.

Lemma triple_Newb_con2 : forall (l1 l2:listint),
  triple (Newf_blk2 (val_listint l1) (val_listint l2))
    (\R[\f[], \b[] ])
    (fun r => \exists bp1 bp2,
      (\exists fp : floc,\[r = fp] \*
        (\R[ fp ~f~> (bp1 :: bp2 :: nil),bp1 ~b~> l1 \b* bp2 ~b~> l2]))).
Proof.
  intros. applys* triple_app_fun2.
  simpl. applys triple_let triple_Create_blk2.
  intros v. ext. intros bp1. ext. intros bp2. ext.
  applys triple_conseq_frame triple_fcreate.
  rewrite hstar_hempty_r'.
  apply himpl_noduplicate2.
  intros r. rewrite hstar_hempty_r.
  intros h M. exists~ bp1 bp2.
Qed.


(*-------- create a file with three blocks -----------*)
Definition Create_blk3 : val :=
  Fun 'l1 'l2 'l3 :=
    Let 'lb := Create_blk2 'l2 'l1 in
    Let 'bk := 'bcreate 'l3 in
    Let 'lb1 := 'bk 'b+ 'lb in
    'frev 'lb1.

Lemma triple_Create_blk3 : forall Hf (l1 l2 l3:listint),
  triple (Create_blk3 (val_listint l1) (val_listint l2) (val_listint l3))
    (\R[Hf, \b[] ])
    (fun r => \exists p1 p2 p3, \[r = val_listbloc (rev (p3 :: p2 :: p1 :: nil))] \*
              (\R[ Hf, (p1 ~b~> l1 \b* p2 ~b~> l2 \b* p3 ~b~> l3)])).
Proof.
  intros. applys* triple_app_fun3. simpl.
  applys triple_let triple_Create_blk2.
  ext. intros bp2. ext. intros bp1. ext.
  applys triple_let.
  applys triple_conseq_frame triple_bcreate'.
  outer_emp. inner_femp.
  ext. intros bp3. rewrite hbstar_assoc. ext.
  applys triple_let triple_fbuffer_list. ext.
  applys triple_conseq_frame triple_frev_blist.
  outer_emp.
  { intros r h. rewrite hstar_hempty_r', hstar_hpure, hbstar_comm3.
    intros (MA&MB). exists~ bp1 bp2 bp3. rewrite hstar_hpure. splits~. }
Qed.

Definition Newf_blk3 :val := 
  Fun 'ln1 'ln2 'ln3 :=
    Let 'lb := Create_blk3 'ln1 'ln2 'ln3 in
    'fcreate 'lb.

Lemma triple_Newf_blk3 : forall (l1 l2 l3:listint),
  triple (Newf_blk3 (val_listint l1) (val_listint l2) (val_listint l3))
    (\R[\f[], \b[] ])
    (fun r => \exists bp1 bp2 bp3,
      (\exists fp : floc, \[r = fp] \*
        (\R[ fp ~f~> rev (bp3 :: bp2 :: bp1 :: nil),
           bp1 ~b~> l1 \b* bp2 ~b~> l2 \b* bp3 ~b~> l3]))).
Proof.
  intros. applys triple_app_fun3.
  reflexivity. auto.
  simpl. applys triple_let.
  applys triple_Create_blk3.
  ext. intros bp1. ext. intros bp2. ext. intros bp3. ext.
  applys triple_conseq_frame triple_fcreate.
  rewrite hstar_hempty_r'.
  apply himpl_noduplicate3.
  intros v. rewrite hstar_hempty_r'.
  intros h M. exists~ bp1 bp2 bp3.
Qed.


(*===================== Copy a file ===========================*)
(*Copy the entire file, starting with the i-th block
  and storing the new block location list in the buffer*)
Definition Copy_f_buffer := 
  Fix 'F 'f 'i :=
    Let 'n := 'fsize 'f in
    Let 'be := ('i '= 'n) in
    If_ 'be
    Then (val_listbloc nil)
    Else
      Let 'bk1 := 'nth_blk 'f 'i in
      Let 'i := 'i '+ 1 in
      Let 'bk := (Copy_blk 'bk1) in 
      Let 'lb := 'F 'f 'i in
      'bk 'b+ 'lb .
 
Lemma triple_Copy_f_buffer:  forall f1 p1 ln,
  triple (Copy_f_buffer (val_floc f1) 0)
    (\R[f1 ~f~> (p1::nil),(p1 ~b~> ln)])
    (fun r => \exists p1', \[r = val_listbloc (p1' :: nil)] \* 
              \R[f1 ~f~> (p1::nil), ((p1' ~b~> ln) \b* (p1 ~b~> ln))]).
Proof.
  exp_fix. fix_body.
  applys triple_let triple_Copy_blk.
  ext. intros bp1. ext.
  applys triple_let. 
  
  exp_fix.
  applys triple_val'. ext.
  applys triple_conseq_frame triple_fbuffer_list.
  outer_emp.
  intros r. rewrite hstar_hempty_r'.
  intros h M. exists~ bp1.
Qed.

Definition Copy_f :=
  Fun 'f :=
    Let 'lb := Copy_f_buffer 'f 0 in
    'fcreate 'lb.

Lemma triple_Copy_f:  forall f1 p1 ln,
  triple (Copy_f (val_floc f1))
    (\R[f1 ~f~> (p1::nil),(p1 ~b~> ln)])
    (fun r => \exists f2 p1', \[r = val_floc f2] \*
           \R[ f2 ~f~> (p1'::nil) \f* f1 ~f~> (p1::nil), 
              ((p1' ~b~> ln) \b* (p1 ~b~> ln))]).
Proof.
  intros. applys* triple_app_fun. simpl.
  applys triple_let triple_Copy_f_buffer.
  ext. intros p1'. ext.
  applys triple_conseq_frame triple_fcreate.
  rewrite hstar_sep. intros h (MA&MB). split.
  rewrite hfstar_hpure. split.
  apply noduplicates_one. apply MA.
  apply MB.
  intros r. intros h M.
  rewrite hstar_hexists in M.
  destruct M as (f2&M).
  rewrite hstar_assoc, hstar_hpure in M.
  destruct M as (MA&MB).
  rewrite hstar_sep in MB.
  exists f2 p1'. rewrite hstar_hpure. splits~.
Qed.