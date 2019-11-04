{-# LANGUAGE DeriveGeneric, StandaloneDeriving #-}

module JSON.GenericDerive where

import Prelude
import AST
import Skeleton
import ProgramDef
import Prettyprinter.Definitions
import Names

import Plumbing

import Data.Aeson
import GHC.Generics

deriving instance Generic ScopedName
deriving instance Generic Coq_expr
deriving instance Generic Coq_skeleton
deriving instance Generic Coq_program

deriving instance Show Coq_skeleton
deriving instance Show Coq_program

deriving instance Eq Coq_skeleton
deriving instance Eq Coq_program

instance ToJSON ScopedName where
    toEncoding = genericToEncoding defaultOptions
instance FromJSON ScopedName where

instance ToJSON Coq_expr where
    toEncoding = genericToEncoding defaultOptions
instance FromJSON Coq_expr where

instance ToJSON Coq_program where
    toEncoding = genericToEncoding defaultOptions
instance FromJSON Coq_program where

instance ToJSON Coq_skeleton where
    toEncoding = genericToEncoding defaultOptions
instance FromJSON Coq_skeleton where

instance ToJSON PrettyPrinterConfig where
    toEncoding = genericToEncoding defaultOptions
instance FromJSON PrettyPrinterConfig where
