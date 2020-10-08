module Keys where

import qualified Prelude
import qualified Maps

type Coq_key_identifier = Prelude.Int

data Coq_key_usage =
   Encryption
 | Signing

data Coq_key_type =
   SymKey
 | AsymKey

data Coq_key =
   MkCryptoKey Coq_key_identifier Coq_key_usage Coq_key_type

type Coq_key_permission = (,) Coq_key_identifier Prelude.Bool

type Coq_keys = Maps.NatMap__Coq_t Coq_key

type Coq_key_perms = Maps.NatMap__Coq_t Prelude.Bool

