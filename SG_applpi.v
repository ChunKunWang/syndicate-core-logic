Add LoadPath "/home/amos/applpi".
(** https://github.com/syndicate-storage/syndicate-core/blob/master/protobufs/sg.proto *)

Require Import libapplpi.
Require Import SG_applpi_string.
Require Import SG_fs.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.
Import ListNotations.

(** Result channel *)
Axiom result_chan : chan unit false.
Definition succ : proc := OutAtom result_chan tt.

(** Catch IO exception *)
Axiom IOexn_chan : chan unit false.
Definition IOexn := OutAtom IOexn_chan tt.

(** Catch a system failure *)
Axiom system_failure_chan : chan unit false.
Definition failure := OutAtom system_failure_chan tt.

Definition may_fail := nuP
  (fun x => parP (InAtom x)
    (parP (OutAtom x tt) (x ?? (fun _ => OutAtom system_failure_chan tt)))).

(** Manifest data plane *)
(* c.f. protobufs/sg.proto: l.44-60 *)
Record Manifest : Set := manifest
  { volume_id : string;
    owner_id : string;
    file_id : string;
    size : string}.

(** Definition of Syndicate requests from client *)
(* c.f. protobufs/sg.proto: l.80-94 *)
Inductive SG_req : Set :=
  | req_write : string -> nat -> bool -> SG_req
  | req_truncate: string -> SG_req
  | req_detach: string -> SG_req
  | req_rename: string -> SG_req
  | req_putchunks: string -> SG_req
  | req_deletechunks: string -> SG_req
  | req_setxattr: string -> SG_req
  | req_removexattr: string -> SG_req
  | req_reload: string -> SG_req
  | req_refresh: string -> SG_req
  | req_rename_hint: string -> SG_req.

Record md_HTTP_connection_data : Set := con_data
  { header_message : SG_req}.

Definition InputStream : Set := chan SG_req true.

(** Response messages *)
Inductive RespMsg : Set :=
  | resp_write : RespMsg
  | resp_truncate : RespMsg
  | resp_detach : RespMsg
  | resp_rename : RespMsg
  | resp_putchunks : RespMsg
  | resp_deletechunks : RespMsg
  | resp_setxattr : RespMsg
  | resp_removexattr : RespMsg
  | resp_reload : RespMsg
  | resp_refresh : RespMsg
  | resp_rename_hint : RespMsg.

Definition OutputStream := chan RespMsg true.

Record SGstate : Set := sg_state
  {in_stream : InputStream;
   to_client : OutputStream;
(* Manifest info *)
   from_client : Manifest;
(* file system is modeled as a process *)
   to_fs : FileSystemState }.

Definition update_from (st : SGstate) (data: Manifest) : SGstate := 
  sg_state (in_stream st) (to_client st)
  data (to_fs st).

Definition STATE : Set := SGstate.

Definition reply (r : RespMsg) (c : OutputStream) (cont : proc) : proc :=
  c << r >> cont.

Definition get_req (c : InputStream) (cont : SG_req -> proc) : proc :=
  c ?? cont.

(* a -> b -> c => a * b -> c*)

Definition sample_server (i:chan (nat * (chan nat true)) false) : proc := 
    rinP i (fun ar => let a := fst ar in let r := snd ar in OutAtom r (plus a 1)).

Definition sample_client (i:chan (nat * (chan nat true)) false) (o:chan nat true) : proc :=
    nuPl (fun r => parP (OutAtom i (0,r)) (inP r (fun x => OutAtom o x))).

Definition sample_Run (i : chan (nat * (chan nat true)) false) (o : chan nat true) := 
  (parP (sample_server i) (sample_client i o)).


(*Definition server (i:chan (md_HTTP_connection_data * (chan RespMsg true)) false) : proc := 
    rinP i (fun ar => let a := fst ar in let r := snd ar in 
                        match a with 
                          | con_data msg => match msg with
                                            | req_write request => OutAtom r resp_write
                                            | req_truncate request => OutAtom r resp_truncate
                                            | req_detach request => OutAtom r resp_detach
                                            | req_rename request => OutAtom r resp_rename
                                            | req_putchunks request => OutAtom r resp_putchunks
                                            | req_deletechunks request => OutAtom r resp_deletechunks
                                            | req_setxattr request => OutAtom r resp_setxattr
                                            | req_removexattr request => OutAtom r resp_removexattr
                                            | req_reload request => OutAtom r resp_reload
                                            | req_refresh request => OutAtom r resp_refresh
                                            | req_rename_hint request => OutAtom r resp_rename_hint
                                          end
                          end).

Definition client (req:md_HTTP_connection_data) (i:chan (md_HTTP_connection_data * (chan RespMsg true)) false) (o:chan RespMsg true) : proc :=
    nuPl (fun r => parP (OutAtom i (req,r)) (inP r (fun x => OutAtom o x))).

Definition Run (req:md_HTTP_connection_data) (i:chan (md_HTTP_connection_data * (chan RespMsg true)) false) (o:chan RespMsg true) := 
  (parP (server i) (client req i o)).
*)
(** Syndicate Server State: contain a list of SGstate as a logical time *)
Record SGServerState : Set := sg_server_st
  {server_st : list bool}.

Fixpoint Create_ServerState (SerStatus : bool) (server_st : list bool) : option (list bool) :=
  match server_st with
    | [] => Some [SerStatus]
    | hd::tl => match Create_ServerState SerStatus tl with
                  | None => None
                  | Some a => Some (hd::a)
                end
  end.

Definition Update_Server_State (server_status : bool) (SG_server : SGServerState) : option SGServerState :=
  match SG_server with
    | sg_server_st st => match Create_ServerState server_status st with
                          | None => None
                          | Some new => Some (sg_server_st new)
                        end
  end.

Inductive FS_req : Set :=
  | freq_write : string -> nat -> bool -> FS_req
  | freq_truncate: string -> FS_req
  | freq_detach: string -> FS_req
  | freq_rename: string -> FS_req
  | freq_putchunks: string -> FS_req
  | freq_deletechunks: string -> FS_req
  | freq_setxattr: string -> FS_req
  | freq_removexattr: string -> FS_req.

Inductive FSRespMsg : Set :=
  | fresp_write : FSRespMsg
  | fresp_truncate : FSRespMsg
  | fresp_detach : FSRespMsg
  | fresp_rename : FSRespMsg
  | fresp_putchunks : FSRespMsg
  | fresp_deletechunks : FSRespMsg
  | fresp_setxattr : FSRespMsg
  | fresp_removexattr : FSRespMsg.

Definition client_test (req:md_HTTP_connection_data) (i:chan (md_HTTP_connection_data * (chan RespMsg true)) false) (o:chan RespMsg true) : proc :=
    nuPl (fun r => parP (OutAtom i (req,r)) (inP r (fun x => OutAtom o x))).


Definition server_test (i:chan (md_HTTP_connection_data * (chan RespMsg true)) false) 
                       (f_in: chan FS_req true)
                       (f_out: chan FSRespMsg true) : proc := 
    rinP i (fun ar => let a := fst ar in let r := snd ar in 
                        match a with 
                          | con_data msg => match msg with
                                            | req_write req_fname req_offset req_content => outP f_in (freq_write req_fname req_offset req_content) 
                                                                 (inP f_out (fun c => match c with
                                                                                       | fresp_write => OutAtom r resp_write
                                                                                       | _ => OutAtom r resp_write
                                                                                      end))
                                            | _ => OutAtom r resp_write
                                          end
                          end).


Definition fs_test (f_in:chan FS_req false) (f_out:chan FSRespMsg true) (f_st:chan FileSystemState true) : proc :=
    rinP f_in (fun a => match a with 
                       | freq_write fname foffset fcontent => inP f_st (fun fst => match FS_Write_Main fname foffset fcontent fst with
                                                                          | None => outP f_st fst (OutAtom f_out fresp_write)
                                                                          | Some new_st => outP f_st new_st (OutAtom f_out fresp_write)
                                                                        end)
                       | _ => OutAtom f_out fresp_write
                     end).




