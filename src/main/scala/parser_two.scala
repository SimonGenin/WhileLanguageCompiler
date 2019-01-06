import scala.collection.mutable
import scala.util.parsing.combinator._
import scala.collection.mutable.Map
import scala.util.matching.Regex
import scala.util.parsing.input.{NoPosition, Position, Reader}

/*
The While language:

<expr> ::= (var <integer>)
        | (quote <integer>)
        | (cons <expr> <expr>)
        | (hd <expr>)
        | (tl <expr>)
        | (=? <expr> <expr>)

<instr> ::= (:= (var <integer>) <expr> )
          | (; <instr> <instr>)
          | (while e <instr>)
*/

sealed class WhileToken

case class IDENTIFIER(str: String) extends WhileToken
case class LITERAL(str: String) extends WhileToken
case object VAR extends WhileToken
case object QUOTE extends WhileToken
case object CONS extends WhileToken
case object HD extends WhileToken
case object TL extends WhileToken
case object COMP extends WhileToken
case object ASSIGN extends WhileToken
case object SEMI_COLON extends WhileToken
case object WHILE_TOKEN extends WhileToken
case object O_P extends WhileToken
case object C_P extends WhileToken


trait WhileCompilationError
case class WhileLexerError(msg: String) extends WhileCompilationError


object WhileLexer extends RegexParsers {


    override def skipWhitespace = true
    override val whiteSpace: Regex = "[ \t\r\f\n]+".r

    def _var: WhileLexer.Parser[VAR.type] = "var"           ^^^ VAR
    def _quote: WhileLexer.Parser[QUOTE.type] = "quote"     ^^^ QUOTE
    def _cons: WhileLexer.Parser[CONS.type] = "cons"        ^^^ CONS
    def _hd: WhileLexer.Parser[HD.type] = "hd"              ^^^ HD
    def _tl: WhileLexer.Parser[TL.type] = "tl"              ^^^ TL
    def _comp: WhileLexer.Parser[COMP.type] = "?="          ^^^ COMP
    def _assign: WhileLexer.Parser[ASSIGN.type] = ":="      ^^^ ASSIGN
    def _semicolon: WhileLexer.Parser[SEMI_COLON.type] = ";"         ^^^ SEMI_COLON
    def _while: WhileLexer.Parser[WHILE_TOKEN.type] = "while"     ^^^ WHILE_TOKEN
    def _op: WhileLexer.Parser[O_P.type] = "("              ^^^ O_P
    def _cp: WhileLexer.Parser[C_P.type] = ")"              ^^^ C_P

    def _identifier: Parser[IDENTIFIER] = {
        "[a-zA-Z_][a-zA-Z0-9_]*".r ^^ { str => IDENTIFIER(str) }
    }

    def _literal: Parser[LITERAL] = {
        """[0-9]+""".r ^^ { str => LITERAL(str) }
    }


    def _tokens: Parser[List[WhileToken]] = {
        phrase(rep1(_op | _cp | _var | _quote | _cons | _hd | _tl | _comp | _assign
            | _semicolon | _while | _literal | _identifier))
    }

    def apply(code: String): Either[WhileLexerError, List[WhileToken]] = {
        parse(_tokens, code) match {
            case NoSuccess(msg, next) => Left(WhileLexerError(msg))
            case Success(result, next) => Right(result)
        }
    }
}

sealed trait WhileAST

case class Constructor ( left: WhileAST, right: WhileAST ) extends WhileAST {

    "λxy. (λz. z x y)" + " " + "(" + left.toString + ")" + " " + "(" + right.toString + ")"

}
case class UseVariable(str: String, store: mutable.Map[String, String]) extends WhileAST {
    override def toString: String = {
        MakeNumeric(store(str), true).toString
    }
}

case class MakeNumeric(value: String, formattedAsLambda : Boolean = false) extends WhileAST {

    override def toString: String = {

        if (formattedAsLambda) return value

        if (value.toInt == 0) "λsz.z"
        if (value.toInt == 1) "λsz.sz"

        var total = ""
        var totalClosing = ""
        for (i <- 2 to value.toInt) {

            total += "(s"
            totalClosing += ")"

        }

        "λsz.s" + total + "z" + totalClosing

    }

}

case class Head(ast: WhileAST) extends WhileAST {

    override def toString: String = {
        val T = "λxy.x"
        "λp.p" + T +  " (" + ast.toString + ")"
    }

}
case class Tail(ast: WhileAST) extends WhileAST {

    val F = "λxy.y"
    "λp.p" + F + " (" + ast.toString + ")"

}
case class Comparaison(left: WhileAST, right: WhileAST) extends WhileAST {


   // A predicate is a function that returns a boolean value. The most fundamental predicate is ISZERO, which returns TRUE if its argument is the Church numeral 0, and FALSE if its argument is any other Church numeral:

   //     ISZERO := λn.n (λx.FALSE) TRUE
   // The following predicate tests whether the first argument is less-than-or-equal-to the second:

   //     LEQ := λm.λn.ISZERO (SUB m n),
   // and since m = n, if LEQ m n and LEQ n m, it is straightforward to build a predicate for numerical equality.

    val T = "(λxy.x)"
    val F = "(λxy.y)"
    // val ¬ = "(λx. x " + F + T +")"

    // val ISZERO = "λx. x " + F + ¬ + F

    // λst.(sFTTt)(sT(tFT))F
    val EQUALITY = "λst.(s" + F + T + T + "t)(s" + T + "(t" + F + T + "))" + F

    override def toString: String = {
        EQUALITY + "(" + left.toString + ")" + " " + "(" + right.toString + ")"
    }


}
case class WhileExecution(expression: WhileAST, statement: WhileAST) extends WhileAST {

    override def toString: String = {

        val Y = "λy.(λx.y(xx))(λx.y(xx))"
        val r = statement.toString
        val n = expression.toString

        val T = "(λxy.x)"
        val F = "(λxy.y)"
        val not = s"(λx. x $F$T)"

        val Z = s"λx. x $F $not $F"

        val S = "λwyx. y (w y x)"

        val ADD = s"λxy. x ($S) y"

        // val w = s"λrn. $Z n 0 (r ( ($ADD) n (${MakeNumeric("1").toString}) ) )"
        val w = s"λrn. $Z n 0 (r (n) )"

        s"$Y ($w $r $n)"

    }

}


case class Nothing() extends WhileAST {
    override def toString: String = ""
}

case class ExecuteStatement(s1: WhileAST, s2: WhileAST) extends WhileAST {

    override def toString: String = {

        s2.toString + "(" + s1.toString + ")"

    }

}

case class StoreVariable(name: String, valueExp: WhileAST, store: mutable.Map[String, String]) extends WhileAST {

    override def toString: String = ""

}

object StoreVariable {
    def apply(name: String, valueExp: WhileAST, store: mutable.Map[String, String]): StoreVariable = {

        println(s"Adding variable $name into the store with value $valueExp")
        store.put(name, valueExp.toString)

        new StoreVariable(name, valueExp, store)
    }
}

object WhileParser extends Parsers
{
    override type Elem = WhileToken

    val store: mutable.Map[String, String] = mutable.Map()

    class WhileTokenReader(tokens: Seq[WhileToken]) extends Reader[WhileToken] {
        override def first: WhileToken = tokens.head
        override def atEnd: Boolean = tokens.isEmpty
        override def pos: Position = NoPosition
        override def rest: Reader[WhileToken] = new WhileTokenReader(tokens.tail)
    }

    private def literal: Parser[LITERAL] = {
        accept("string literal", { case lit @ LITERAL(name) => lit })
    }

    def expression: Parser[WhileAST] = {

        val constant = {
            O_P ~ QUOTE ~ literal ~ C_P ^^ {
                case  _ ~ _ ~ LITERAL(value)  ~ _ => MakeNumeric(value)
            }
        }

        val variable = {
            O_P ~ VAR ~ literal ~ C_P ^^ {
                case  _ ~ _ ~ LITERAL(value) ~ _ => UseVariable(value, store)
            }
        }

        val constructor = {
            O_P ~ CONS ~ expression ~ expression ~ C_P ^^ {
                case  _ ~ _ ~ exp ~ exp2 ~ _ =>  Constructor(exp, exp2)
            }
        }

        val head = {
            O_P ~ HD ~ expression ~ C_P ^^ {
                case  _ ~ _ ~ exp ~ _ => Head(exp)
            }
        }

        val tail = {
            O_P ~ TL ~ expression ~ C_P ^^ {
                case  _ ~ _ ~ exp ~ _ => Tail(exp)
            }
        }

        val comparaison = {
            O_P ~ COMP ~ expression ~ expression ~ C_P ^^ {
                case  _ ~ _ ~ exp ~ exp2 ~ _ => Comparaison(exp, exp2)
            }
        }

        constant | variable | constructor | head | tail | comparaison
    }

    def statement: Parser[WhileAST] = {


        val assignation = {
            O_P ~ ASSIGN ~ O_P ~ VAR ~ literal ~ C_P ~ expression ~ C_P ^^ {
                case _ ~ _ ~ _ ~ _ ~ LITERAL(name) ~ _ ~ valueExp ~ _  => StoreVariable(name, valueExp, store)
            }
        }

        val following = {
            O_P ~ SEMI_COLON ~ statement ~ statement ~ C_P ^^ {
                case _ ~ _ ~ s1 ~ s2 ~ _  => ExecuteStatement(s1, s2)
            }
        }

        val whileStatement = {
            O_P ~ WHILE_TOKEN ~ expression ~ statement ~ C_P ^^ {
                case _ ~ _ ~ exp ~ s ~ _ => WhileExecution(exp, s)
            }
        }

        val test = {
            O_P ~ C_P ^^ {
                case _ ~ _ => Nothing()
            }
        }

         whileStatement  | following | assignation | test

    }

    def apply(tokens: Seq[WhileToken]): Either[WhileParserError, WhileAST] = {
        val reader = new WhileTokenReader(tokens)
        statement(reader) match {
            case NoSuccess(msg, next) => Left(WhileParserError(msg))
            case Success(result, next) => Right(result)
        }
    }


}

case class WhileParserError(msg: String) extends WhileCompilationError

object TestWhileParser  {
    def main(args: Array[String]): Unit = {

        // yolo print(WhileCompiler("(:= (var (quote 5)) )"))
        // print(WhileCompiler("( ; (:= (var 5) (quote 3) ) ( while (?= (var 5) (var 5)) ( := (var 2) (quote 1) ) ) )"))
        print(WhileCompiler("( while (quote ) () )"))
        // print(WhileCompiler("(cons (var 5) (quote 4))"))

        // (:= (var 5) (quote 3) )
        // ( while (var 5) ( := (var 2) (quote 1) ) )
        // ( ; )
        // ( ; (:= (var 5) (quote 3) ) ( while (var 5) ( := (var 2) (quote 1) ) ) )

    }
}

object WhileCompiler {
    def apply(code: String): Either[WhileCompilationError, WhileAST] = {
        for {
            tokens <- WhileLexer(code).right
            ast <- WhileParser(tokens).right
        } yield ast
    }
}