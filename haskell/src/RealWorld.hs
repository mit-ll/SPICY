{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module RealWorld where

import qualified Prelude
import qualified Common
import qualified Keys
import qualified Maps
import qualified Messages
import qualified Specif

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

type RW_message__Coq_access = Keys.Coq_key_permission

data Coq_message__Coq_message =
   Coq_message__Permission RW_message__Coq_access
 | Coq_message__Content Prelude.Int
 | Coq_message__MsgPair Messages.Coq_type Messages.Coq_type Coq_message__Coq_message Coq_message__Coq_message

_Coq_message__message_rect :: (RW_message__Coq_access -> a1) -> (Prelude.Int -> a1) -> (Messages.Coq_type
                              -> Messages.Coq_type -> Coq_message__Coq_message -> a1 ->
                              Coq_message__Coq_message -> a1 -> a1) -> Messages.Coq_type ->
                              Coq_message__Coq_message -> a1
_Coq_message__message_rect f f0 f1 _ m =
  case m of {
   Coq_message__Permission acc -> f acc;
   Coq_message__Content n -> f0 n;
   Coq_message__MsgPair t1 t2 m1 m2 ->
    f1 t1 t2 m1 (_Coq_message__message_rect f f0 f1 t1 m1) m2 (_Coq_message__message_rect f f0 f1 t2 m2)}

_Coq_message__message_rec :: (RW_message__Coq_access -> a1) -> (Prelude.Int -> a1) -> (Messages.Coq_type
                             -> Messages.Coq_type -> Coq_message__Coq_message -> a1 ->
                             Coq_message__Coq_message -> a1 -> a1) -> Messages.Coq_type ->
                             Coq_message__Coq_message -> a1
_Coq_message__message_rec =
  _Coq_message__message_rect

type Coq_message__Coq_typeDenote = Any

_Coq_message__extractContent :: Coq_message__Coq_message -> Prelude.Int
_Coq_message__extractContent msg =
  case msg of {
   Coq_message__Content t -> t;
   _ -> __}

_Coq_message__extractPermission :: Coq_message__Coq_message -> RW_message__Coq_access
_Coq_message__extractPermission msg =
  case msg of {
   Coq_message__Permission a -> a;
   _ -> __}

_Coq_message__msgFst :: Messages.Coq_type -> Messages.Coq_type -> Coq_message__Coq_message ->
                        Coq_message__Coq_message
_Coq_message__msgFst _ _ msg =
  case msg of {
   Coq_message__MsgPair _ _ m1 _ -> m1;
   _ -> __}

_Coq_message__msgSnd :: Messages.Coq_type -> Messages.Coq_type -> Coq_message__Coq_message ->
                        Coq_message__Coq_message
_Coq_message__msgSnd _ _ msg =
  case msg of {
   Coq_message__MsgPair _ _ _ m2 -> m2;
   _ -> __}

type Coq_cipher_id = Prelude.Int

data Coq_crypto =
   Content Messages.Coq_type Coq_message__Coq_message
 | SignedCiphertext Messages.Coq_type Coq_cipher_id

data Coq_msg_pat =
   Accept
 | Signed Keys.Coq_key_identifier Prelude.Bool
 | SignedEncrypted Keys.Coq_key_identifier Keys.Coq_key_identifier Prelude.Bool

type Coq_msg_seq = (,) (Prelude.Maybe Common.Coq_user_id) Prelude.Int

data Coq_cipher =
   SigCipher Messages.Coq_type Keys.Coq_key_identifier Common.Coq_user_id Coq_msg_seq Coq_message__Coq_message
 | SigEncCipher Messages.Coq_type Keys.Coq_key_identifier Keys.Coq_key_identifier Common.Coq_user_id 
 Coq_msg_seq Coq_message__Coq_message

type Coq_queued_messages = ([]) (Specif.Coq_sigT Messages.Coq_type Coq_crypto)

type Coq_ciphers = Maps.NatMap__Coq_t Coq_cipher

type Coq_my_ciphers = ([]) Coq_cipher_id

type Coq_recv_nonces = ([]) Coq_msg_seq

type Coq_sent_nonces = ([]) Coq_msg_seq

data Coq_user_cmd_type =
   Base Messages.Coq_type
 | Message Messages.Coq_type
 | Crypto Messages.Coq_type
 | UPair Coq_user_cmd_type Coq_user_cmd_type

type Coq_denote = Any

data Coq_user_cmd =
   Return Coq_user_cmd_type Coq_denote
 | Bind Coq_user_cmd_type Coq_user_cmd_type Coq_user_cmd (Coq_denote -> Coq_user_cmd)
 | Gen
 | Send Messages.Coq_type Common.Coq_user_id Coq_crypto
 | Recv Messages.Coq_type Coq_msg_pat
 | SignEncrypt Messages.Coq_type Keys.Coq_key_identifier Keys.Coq_key_identifier Common.Coq_user_id 
 Coq_message__Coq_message
 | Decrypt Messages.Coq_type Coq_crypto
 | Sign Messages.Coq_type Keys.Coq_key_identifier Common.Coq_user_id Coq_message__Coq_message
 | Verify Messages.Coq_type Keys.Coq_key_identifier Coq_crypto
 | GenerateSymKey Keys.Coq_key_usage
 | GenerateAsymKey Keys.Coq_key_usage

data Coq_user_data =
   Coq_mkUserData Keys.Coq_key_perms Coq_user_cmd Coq_queued_messages Coq_my_ciphers Coq_recv_nonces 
 Coq_sent_nonces Prelude.Int

type Coq_honest_users = Common.Coq_user_list Coq_user_data

data Coq_universe =
   Coq_mkUniverse Coq_honest_users Coq_user_data Coq_ciphers Keys.Coq_keys

