{-
   Copyright 2014 huwei04@hotmail.com

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-}

module Type (
  Type(..),
  Scheme(..),
  translateFunType,
  isNestedSignalType
) where

import qualified Text.PrettyPrint as PP

data Type = TVar String
          | TInt
          | TBool
          | TStr
          | TFloat
          | TDouble
          | TCon Type [Type]
          | TCN String
          | TFun [Type] Type
          deriving (Eq, Ord)

data Scheme = Scheme [String] Type deriving (Eq, Ord)

instance Show (Type) where
  showsPrec _ x = shows $ prType x

prType (TVar n) = PP.text n
prType TInt     = PP.text "Int"
prType TBool    = PP.text "Bool"
prType TFloat   = PP.text "Float"
prType TDouble  = PP.text "Double"
prType TStr     = PP.text "String"
prType (TCon a []) = PP.parens $ prType a
prType (TCon a b) = PP.parens $ prType a PP.<+> prTypeList b
prType (TCN a)  = PP.text a
prType (TFun [] a) = PP.parens $ prType a
prType (TFun a b) = PP.parens $ prTypeList a PP.<+> PP.text "->" PP.<+> prType b

prTypeList []       = PP.text ""
prTypeList (x:ps)   = prType x PP.<+> prTypeList ps

instance Show (Scheme) where
  showsPrec _ x = shows $ prScheme x

prScheme (Scheme vars t) = PP.text "forall" PP.<+> (PP.sep $ map (\v -> PP.text v) vars) PP.<+> PP.text "."
                          PP.<+> prType t

translateFunType (TFun [] e) = e
translateFunType (TFun (t:ts) e) = TFun [translateFunType t] (translateFunType $ TFun ts (translateFunType e))
translateFunType t = t


nestedSignalType i (TCon a b) = nestedSignalTypeList (nestedSignalType i a) b
nestedSignalType i (TCN a)  = if a == "Signal" then i + 1 else i
nestedSignalType i (TFun a b) = maximum [(nestedSignalTypeList i a), (nestedSignalType i b)]
nestedSignalType i _ = i

nestedSignalTypeList i [] = i
nestedSignalTypeList i a = maximum (map (nestedSignalType i) a)

isNestedSignalType t = (nestedSignalType 0 t) >= 2
