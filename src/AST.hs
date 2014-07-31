module AST(
  Exp(..),
  Con(..),
  Lit(..),
  exprPos
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.Parsec.Pos (SourcePos)
import qualified Text.PrettyPrint as PP

type EPos = SourcePos

data Exp = EVar  String EPos
         | ELit  Lit EPos
         | ECon  Con EPos
         | EApp  Exp [Exp] EPos
         | EAbs  [Exp] Exp EPos
         | EFun  String [Exp] Exp EPos
         | ELet  [(Exp, Exp)] Exp EPos
         | EIf   Exp Exp Exp EPos
         | ECase Exp [(Exp, Exp)] EPos
         deriving (Eq, Ord)

data Con = CCon String [Exp]
         deriving (Eq, Ord)

data Lit = LInt   Integer
         | LBool  Bool
         | LStr   String
         | LFloat Float
         | LDouble Double
         deriving (Eq, Ord)


exprPos (EVar _ pos) = pos
exprPos (ELit _ pos) = pos
exprPos (ECon _ pos) = pos
exprPos (EApp _ _ pos) = pos
exprPos (EAbs _ _ pos) = pos
exprPos (EFun _ _ _ pos) = pos
exprPos (ELet _ _ pos) = pos
exprPos (EIf _ _ _ pos) = pos
exprPos (ECase _ _ pos) = pos

instance Show (Exp) where
  showsPrec _ x = shows $ prExp x

prExp (EVar n _) = PP.text n
prExp (ELit (LBool True) _) = PP.text "True"
prExp (ELit (LBool False) _) = PP.text "False"
prExp (ELit (LInt i) _) = PP.integer i
prExp (ELit (LFloat f) _) = PP.float f
prExp (ELit (LDouble d) _) = PP.double d
prExp (ELit (LStr s) _) = PP.text s
prExp (ECon (CCon n es) _) = PP.parens $ PP.text n PP.<+> prExpList es
prExp (EApp f [a] _) = PP.parens $ prExp f PP.<+> prExp a
prExp e@(EApp f ps _) = prExp $ translateApp e
prExp (EAbs ps e _) = PP.parens $ PP.text "\\" PP.<+> prExpList ps
                      PP.<+> PP.text "->" PP.<+> prExp e
prExp (EFun n ps e _) = PP.text n PP.<+> prExpList ps PP.<+> PP.text "=" PP.<+> prExp e
prExp (ELet ps e _) = PP.text "let" PP.<+> (PP.sep $ map (\(a, b)->
                      prExp a PP.<+> PP.text "=" PP.<+> prExp b) ps) PP.<+>
                      PP.text "\n" PP.<+> PP.text "in" PP.<+> prExp e
prExp (EIf c a b _) = PP.parens $ PP.text "if" PP.<+> prExp c PP.<+> PP.text "\n" PP.<+> PP.text "then"
                      PP.<+> prExp a PP.<+> PP.text "\n" PP.<+> PP.text "else" PP.<+> prExp b
prExp (ECase e ps _) = PP.text "case" PP.<+> prExp e PP.<+> PP.text "of"
                       PP.<+> (PP.sep $ map (\(a, b)-> PP.text "\n" PP.<+>
                       prExp a PP.<+> PP.text "->" PP.<+> prExp b) ps)

prExpList [] = PP.text ""
prExpList (x:ps) = prExp x PP.<+> prExpList ps

translateApp e@(EApp f [a] pos) = e
translateApp (EApp f (t:l) pos) = translateApp $ EApp (EApp f [t] pos) l pos