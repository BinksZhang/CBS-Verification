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

Date : 2023.01.06
*)

From SLF (* TLC *) Require Export LibCore TLCbuffer.
From SLF (* Sep *) Require Export TripleAndRules.

Notation "[ ]" := nil (format "[ ]") : liblist_scope.
Notation "[ x ]" := (cons x nil)  : liblist_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : liblist_scope.


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

Lemma san : forall (P Q R:Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R. intros H1 H2 H3.
  apply H2. apply H1. apply H3.
Qed.

(* !! Need to read the Language.v firstly !! *)
Export NotationForTrm.
Export NotationForVariables.

Open Scope val_scope.
Open Scope trm_scope.
Open Scope Z_scope.

(*========================= Copy a block ================================*)

Definition Copy_blk : val := 
  Fun 'f 'n :=                       
  	Let 'b := 'nthblk 'f 'n in  
    Let 'ln := 'bget 'b in
      'bcreate 'ln.

(* Unoptimized coding forms *)
Definition Copy_blk' : val := 
Fun 'f 'n := (
  Let 'b := trm_app
              (trm_app (trm_val (val_fprim fprim_nthblk))
                       (trm_var 'f)) (trm_var 'n) in
  Let 'ln := trm_app (trm_val (val_bprim bprim_get)) (trm_var 'b) in
  trm_app (trm_val (val_bprim bprim_create)) (trm_var 'ln)).

(* Consistent in both forms, our optimized codes are more readable *)
Fact equiv_Copy: Copy_blk = Copy_blk'.
Proof. reflexivity. Qed.

(* the specification and proof of copy a block *)
Lemma triple_Copy_blk : forall (f:floc) (b:bloc) (lb:list bloc) (ln:list int) (n:int),
  triple (Copy_blk f n)
    (\[b = (nth_default bnull (Z.to_nat n) lb)] \* (\R[f ~f~> lb, b ~b~> ln]) )
    (fun r => \exists b1,\[r=(val_bloc b1)] \* (\R[f ~f~> lb,(b1 ~b~> ln) \b* (b ~b~> ln)])).
Proof.
  intros. apply triple_hpure. intros ->.
  eapply triple_app_fun2. reflexivity. auto. simpl.
  eapply triple_let. apply triple_fget_nth_blk.
  intros. simpl.
  apply triple_hpure. intros ->.
  applys triple_let triple_bget. ext.
  applys triple_conseq_frame triple_bcreate.
  rewrite* hstar_hempty_l'.
  introv M. rewrite hstar_hexists in M.
  destruct M as (b1&M).
  rewrite hstar_assoc, hstar_sep, hfstar_hempty_l in M.
  exists~ b1.
Qed.

(* Another spec that directly takes pure fact as the premise *)
Lemma triple_Copy_blk' : forall (f:floc) (b:bloc) (lb:list bloc) (ln:list int) (n:int),
b = (nth_default bnull (Z.to_nat n) lb) ->
  triple (Copy_blk f n)
    (\R[f ~f~> lb, b ~b~> ln])
    (fun r => \exists b1,\[r=(val_bloc b1)] \* (\R[f ~f~> lb,(b1 ~b~> ln) \b* (b ~b~> ln)])).
Proof.
  introv ->. applys* triple_app_fun2. ext.
  applys triple_let triple_fget_nth_blk. ext.
  applys triple_let triple_bget. ext.
  applys triple_conseq_frame triple_bcreate.
  rewrite* hstar_hempty_l'.
  introv M. rewrite hstar_hexists in M.
  destruct M as (b1&M).
  rewrite hstar_assoc, hstar_sep, hfstar_hempty_l in M.
  exists~ b1.
Qed.

(* Notice: the 1st spec can be directly proved by the 2nd one *)
Lemma triple_Copy_blk'' : forall (f:floc) (b:bloc) (lb:list bloc) (ln:list int) (n:int),
  triple (Copy_blk f n)
    (\[b = (nth_default bnull (Z.to_nat n) lb)] \* (\R[f ~f~> lb, b ~b~> ln]) )
    (fun r => \exists b1,\[r=(val_bloc b1)] \* (\R[f ~f~> lb,(b1 ~b~> ln) \b* (b ~b~> ln)])).
Proof. ext. applys* triple_Copy_blk'. Qed.



(*========================= Move a block ================================*)
Definition Move_blk :=
  Fun 'f 'i :=
    Let 'b := 'nthblk 'f 'i in
    Let 'b1 := Copy_blk 'f 'i in
    'set 'f 'i 'as 'b1 ';
    'bdelete 'b.

Lemma triple_Move_blk : forall (f:floc) (b:bloc) (lb:list bloc) (ln:list int) (n:int),
b = (nth_default bnull (Z.to_nat n) lb) ->
  triple (Move_blk f n)
    (\R[ f ~f~> lb, b ~b~> ln ])
    (fun _ => \exists b',
              (\R[( f ~f~> (LibList.update (to_nat n) b' lb)),(b' ~b~> ln)])).
Proof.
  introv ->.
  applys* triple_app_fun2. simpls.
  applys triple_let triple_fget_nth_blk. ext.
  applys* triple_let triple_Copy_blk'.
  ext. intros b'. ext.
  applys triple_seq.
  apply triple_fset_nth_blk.
  applys triple_conseq_frame triple_bdelete.
  rewrite hstar_sep, hfstar_hempty_r, hbstar_comm.
  applys himpl_refl.
  intros r. rewrite hstar_sep, hfstar_hempty_r, hbstar_hempty_l.
  intros h (MA&MB).
  exists b'. splits~.
Qed.

(* Set Printing Coercions.
	Print Copy_fblk .
	Unset Printing Coercions.

Instance Inhab_listint : Inhab (list int).
Proof using. apply (Inhab_of_val (0::nil) ). Qed.

Instance Inhab_listbloc : Inhab (list bloc).
Proof using. apply (Inhab_of_val (bnull::nil) ). Qed. *)

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
      Let 'bk := 'nthblk 'f 'i in
      Let 'i1 := 'i '+ 1 in
      'bdelete 'bk ';
      'F 'f 'i1.

Lemma triple_Remove_f:  forall Hf Hb (f:floc) (b1 b2 b3 b4:bloc) (lb1 lb2 lb3 lb4:list int),
  Hf = ( f ~f~> (b1::b2::b3::b4::nil) ) ->
  Hb = ( (b1 ~b~> lb1) \b* (b2 ~b~> lb2) \b* (b3 ~b~> lb3) \b* (b4 ~b~> lb4) ) ->
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
Definition ReadFile := 
  Fix 'F 'f 'i :=
    Let 'n := 'fsize 'f in
    Let 'be := ('i '= 'n) in
    If_ 'be
    Then (val_listint nil)
    Else
      Let 'bk := 'nthblk 'f 'i in
      Let 'i1 := 'i '+ 1 in
      Let 'ln := 'bget 'bk in
      Let 'ln1 := 'F 'f 'i1 in
      'ln '++ 'ln1.

Lemma triple_ReadFile: forall Hf Hb (f:floc) (b1 b2 b3:bloc) (n1 n2 n3 n4 n5:int),
  Hf = ( f ~f~> (b1::b2::b3::nil) ) ->
  Hb = ( (b1 ~b~> (n1::n2::nil)) \b* (b2 ~b~> (n3::n4::nil)) \b* (b3 ~b~> (n5::nil)) ) ->
  triple (ReadFile f 0)
    (\R[Hf,Hb])
    (fun r => \[r= val_listint (n1::n2::n3::n4::n5::nil) ] \* \R[Hf,Hb]).
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


Ltac exp_fix_create :=
  applys* triple_app_fix2;
  applys triple_let triple_list_len; ext;
  applys triple_let triple_le; ext;
  applys triple_if; case_if*;
  applys triple_let triple_list_hd_bk; ext;
  applys triple_let triple_list_tl_bk; ext;
  applys triple_let.

Ltac cre_pre :=
  rewrite hstar_sep; rewrite hfstar_hempty_r, hbstar_hempty_l;
  apply himpl_refl.

Ltac cre_ext:=
intros r; simpl; rewrite hstar_hexists;
  applys triple_hexists.

Ltac cre_exp_fix:=
  intros; applys* triple_app_fix2;
  applys triple_let triple_list_len;
  ext; applys triple_let triple_le; ext;
  applys triple_if; case_if*.

(*===================== Create files ===========================*)
Definition CreateBlks : val :=
  Fix 'F 'l 'lb:=
    Let 'm := 'len 'l in
    Let 'be := ('m '<= 2) in
    If_ 'be
    Then 
      Let 'bk := 'bcreate 'l in
        'bk 'b+ 'lb
    Else
      Let 'l1 := 'hdblk 'l in
      Let 'l2 := 'tlblk 'l in
      Let 'bk1 := 'bcreate 'l1 in
      Let 'lb1 := 'bk1 'b+ 'lb in
        'F 'l2 'lb1.

Lemma triple_CreateBlks : forall Hf (n1 n2 n3 n4 n5:int),
  triple (CreateBlks (val_listint (n1::n2::n3::n4::n5::nil)) (val_listbloc nil))
    (\R[Hf, \b[] ])
     (fun r => \exists b1 b2 b3,( \[r=(val_listbloc (b3::b2::b1::nil))] \* 
               (\R[Hf, (b1 ~b~> (n1::n2::nil)) \b* (b2 ~b~> (n3::n4::nil) \b* (b3 ~b~> (n5::nil)))]))).
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

Definition Create_File : val :=
  Fun 'l:=
    Let 'lb1 := CreateBlks 'l (val_listbloc nil) in
    Let 'lb := 'frev 'lb1 in
      'fcreate 'lb.


Lemma triple_Create_File : forall (n1 n2 n3 n4 n5:int),
  triple (Create_File (val_listint (n1::n2::n3::n4::n5::nil)) )
    (\R[\f[], \b[] ])
     (fun r => \exists f b1 b2 b3,( \[r= (val_floc f)] \* 
               (\R[(f ~f~> (b1::b2::b3::nil)), (b1 ~b~> (n1::n2::nil)) \b* (b2 ~b~> (n3::n4::nil) \b* (b3 ~b~> (n5::nil)))]))).
Proof.
  intros. applys* triple_app_fun.
  applys triple_let triple_CreateBlks.
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


(*---------Other methods of creating files (not very smart)------*)
(*--- create a file with two blocks ---*)
Definition Create_blk2 : val :=
  Fun 'ln1 'ln2 :=
    Let 'bk1 := 'bcreate 'ln1 in
    Let 'bk2 := 'bcreate 'ln2 in
    Let 'lb := 'buffer 'bk2 in
    'bk1 'b+ 'lb.

Lemma triple_Create_blk2 : forall Hf (ln1 ln2:list int),
  triple (Create_blk2 (val_listint ln1) (val_listint ln2))
    (\R[Hf, \b[] ])
     (fun r => \exists b1 b2,( \[r=(val_listbloc (b1::b2::nil))] \* 
               (\R[Hf, (b1 ~b~> ln1) \b* (b2 ~b~> ln2)]))).
Proof.
  intros. applys triple_app_fun2. reflexivity. auto.
  simpl. applys triple_let triple_bcreate'.
  ext. intros b1. ext.

  applys triple_let.
  applys triple_conseq_frame triple_bcreate'.
  rewrite hstar_hempty_l'. apply himpl_refl.
  intros v. inner_femp.
  ext. intros b2. rewrite hbstar_assoc. ext.
  applys triple_let triple_new_buffer. ext.
  applys triple_conseq_frame triple_blist_buffer.
  outer_emp.
  { intros r h. rewrite hstar_hempty_r', hstar_hpure, hbstar_comm.
    intros (MA&MB). exists~ b1 b2. rewrite hstar_hpure. splits~. }
Qed.

Definition Newf_blk2 :val := 
  Fun 'ln1 'ln2 :=
    Let 'lb := Create_blk2 'ln1 'ln2 in
    'fcreate 'lb.

Lemma triple_Newb_con2 : forall (ln1 ln2:list int),
  triple (Newf_blk2 (val_listint ln1) (val_listint ln2))
    (\R[\f[], \b[] ])
    (fun r => \exists b1 b2,
      (\exists f : floc,\[r = f] \*
        (\R[ f ~f~> (b1 :: b2 :: nil),b1 ~b~> ln1 \b* b2 ~b~> ln2]))).
Proof.
  intros. applys* triple_app_fun2.
  simpl. applys triple_let triple_Create_blk2.
  intros v. ext. intros b1. ext. intros b2. ext.
  applys triple_conseq_frame triple_fcreate.
  rewrite hstar_hempty_r'. apply himpl_refl.
  intros h M. rewrite hstar_hempty_r'. exists~ b1 b2.
Qed.


(*-------- create a file with three blocks -----------*)
Definition Create_blk3 : val :=
  Fun 'l1 'l2 'l3 :=
    Let 'lb := Create_blk2 'l2 'l1 in
    Let 'bk := 'bcreate 'l3 in
    Let 'lb1 := 'bk 'b+ 'lb in
    'frev 'lb1.

Lemma triple_Create_blk3 : forall Hf (ln1 ln2 ln3:list int),
  triple (Create_blk3 (val_listint ln1) (val_listint ln2) (val_listint ln3))
    (\R[Hf, \b[] ])
    (fun r => \exists b1 b2 b3, \[r = val_listbloc (rev (b3 :: b2 :: b1 :: nil))] \*
              (\R[ Hf, (b1 ~b~> ln1 \b* b2 ~b~> ln2 \b* b3 ~b~> ln3)])).
Proof.
  intros. applys* triple_app_fun3. simpl.
  applys triple_let triple_Create_blk2.
  ext. intros b2. ext. intros b1. ext.
  applys triple_let.
  applys triple_conseq_frame triple_bcreate'.
  outer_emp. inner_femp.
  ext. intros b3. rewrite hbstar_assoc. ext.
  applys triple_let triple_blist_buffer. ext.
  applys triple_conseq_frame triple_blist_rev.
  outer_emp.
  { intros r h. rewrite hstar_hempty_r', hstar_hpure, hbstar_comm3.
    intros (MA&MB). exists~ b1 b2 b3. rewrite hstar_hpure. splits~. }
Qed.

Definition Newf_blk3 :val := 
  Fun 'ln1 'ln2 'ln3 :=
    Let 'lb := Create_blk3 'ln1 'ln2 'ln3 in
    'fcreate 'lb.

Lemma triple_Newf_blk3 : forall (ln1 ln2 ln3:list int),
  triple (Newf_blk3 (val_listint ln1) (val_listint ln2) (val_listint ln3))
    (\R[\f[], \b[] ])
    (fun r => \exists b1 b2 b3,
      (\exists fp : floc, \[r = fp] \*
        (\R[ fp ~f~> rev (b3 :: b2 :: b1 :: nil),
           b1 ~b~> ln1 \b* b2 ~b~> ln2 \b* b3 ~b~> ln3]))).
Proof.
  intros. applys triple_app_fun3.
  reflexivity. auto.
  simpl. applys triple_let.
  applys triple_Create_blk3.
  ext. intros b1. ext. intros b2. ext. intros b3. ext.
  applys triple_conseq_frame triple_fcreate.
  rewrite hstar_hempty_r'. apply himpl_refl. 
  intros h M. rewrite hstar_hempty_r'. exists~ b1 b2 b3.
Qed.


(*===================== Copy a file ===========================*)
(*Copy the entire file, starting with the i-th block
  and storing the new block location list in the buffer*)

(* copy a block directly from block tier *)
Definition Copy_blk_dir : val := 
  Fun 'bk :=
    Let 'ln := 'bget 'bk in
    'bcreate 'ln.

Lemma triple_Copy_blk_dir : forall Hf (b:bloc) (l:list int),
  triple (Copy_blk_dir b)
    (\R[Hf, b ~b~> l] )
    (fun r => \exists b',\[r=(val_bloc b')] \* (\R[Hf,(b' ~b~> l) \b* (b ~b~> l)])).
Proof.
  intros. applys* triple_app_fun.
  applys triple_let triple_bget. ext.
  applys triple_conseq_frame triple_bcreate.
  rewrite* hstar_hempty_l'.
  introv M. rewrite hstar_hexists in M.
  destruct M as (b'&M).
  rewrite hstar_assoc, hstar_sep, hfstar_hempty_l in M.
  exists~ b'.
Qed.

Definition Copy_f_buffer := 
  Fix 'F 'f 'i :=
    Let 'n := 'fsize 'f in
    Let 'be := ('i '= 'n) in
    If_ 'be
    Then (val_listbloc nil)
    Else
      Let 'bk1 := 'nthblk 'f 'i in
      Let 'i := 'i '+ 1 in
      Let 'bk := (Copy_blk_dir 'bk1) in 
      Let 'lb := 'F 'f 'i in
      'bk 'b+ 'lb .
 
Lemma triple_Copy_f_buffer:  forall f1 b1 ln,
  triple (Copy_f_buffer (val_floc f1) 0)
    (\R[f1 ~f~> (b1::nil),(b1 ~b~> ln)])
    (fun r => \exists b1', \[r = val_listbloc (b1' :: nil)] \* 
              \R[f1 ~f~> (b1::nil), ((b1' ~b~> ln) \b* (b1 ~b~> ln))]).
Proof.
  exp_fix. fix_body.
  applys triple_let triple_Copy_blk_dir.
  ext. intros bp1. ext.
  applys triple_let. 
  
  exp_fix.
  applys triple_val'. ext.
  applys triple_conseq_frame triple_blist_buffer.
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
  rewrite hstar_sep, hfstar_hempty_l. apply himpl_refl.
  intros r. intros h M.
  rewrite hstar_hexists in M.
  destruct M as (f2&M).
  rewrite hstar_assoc, hstar_hpure in M.
  destruct M as (MA&MB).
  rewrite hstar_sep in MB.
  exists f2 p1'. rewrite hstar_hpure. splits~.
Qed.

Definition CopyFile :=
  Fun 'f :=
    Let 'ln := ReadFile 'f 0 in
      Create_File 'ln.

Ltac ext_blk :=
rewrite hstar_hexists; apply himpl_hexists_l.

Lemma triple_CopyFile: forall Hf Hb (f:floc) (b1 b2 b3:bloc) (n1 n2 n3 n4 n5:int),
  Hf = ( f ~f~> (b1::b2::b3::nil) ) ->
  Hb = ( (b1 ~b~> (n1::n2::nil)) \b* (b2 ~b~> (n3::n4::nil)) \b* (b3 ~b~> (n5::nil)) ) ->
  triple (CopyFile f)
    (\R[Hf,Hb])
    (fun r => \exists f1 b4 b5 b6,( \[r= (val_floc f1)] \* 
               (\R[(f1 ~f~> (b4::b5::b6::nil) \f* Hf ), 
                   (b4 ~b~> (n1::n2::nil)) \b* (b5 ~b~> (n3::n4::nil))
                   \b* (b6 ~b~> (n5::nil)) \b* Hb ]))).
Proof.
  intros. applys* triple_app_fun. simpl. subst.
  applys triple_let. applys* triple_ReadFile. ext.
  applys triple_conseq_frame triple_Create_File.
  rewrite hstar_hempty_l'. applys himpl_refl. intros r.
  ext_blk. intros f1. ext_blk. intros b4.
  ext_blk. intros b5. ext_blk. intros b6.
  rewrite hstar_assoc, hstar_sep, hbstar_assoc, hbstar_assoc.
  intros h M. exists~ f1 b4 b5 b6.
Qed.