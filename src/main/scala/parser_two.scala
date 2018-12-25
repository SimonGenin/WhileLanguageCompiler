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
case object COLON extends WhileToken
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
    def _colon: WhileLexer.Parser[COLON.type] = ":"         ^^^ COLON
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
            | _colon | _while | _literal | _identifier))
    }

    def apply(code: String): Either[WhileLexerError, List[WhileToken]] = {
        parse(_tokens, code) match {
            case NoSuccess(msg, next) => Left(WhileLexerError(msg))
            case Success(result, next) => Right(result)
        }
    }
}

sealed trait WhileAST
case class Numeric (value: Int) extends WhileAST
case class Constructor ( left: WhileAST, right: WhileAST ) extends WhileAST
case class UseVariable(str: String) extends WhileAST
case class MakeNumeric(str: String) extends WhileAST
case class Head(t: WhileAST) extends WhileAST
case class Tail(t: WhileAST) extends WhileAST
case class Comparaison(t: WhileAST, t1: WhileAST) extends WhileAST
case class WhileExecution(t: WhileAST, t1: WhileAST) extends WhileAST
case class ExecuteStatement(t: WhileAST, t1: WhileAST) extends WhileAST
case class StoreVariable(str: String, str1: String) extends WhileAST

object WhileParser extends Parsers
{
    override type Elem = WhileToken

    class WhileTokenReader(tokens: Seq[WhileToken]) extends Reader[WhileToken] {
        override def first: WhileToken = tokens.head
        override def atEnd: Boolean = tokens.isEmpty
        override def pos: Position = NoPosition
        override def rest: Reader[WhileToken] = new WhileTokenReader(tokens.tail)
    }

    private def identifier: Parser[IDENTIFIER] = {
        accept("identifier", { case id @ IDENTIFIER(name) => id })
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
                case  _ ~ _ ~ LITERAL(value) ~ _ => UseVariable(value)
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
                case _ ~ _ ~ _ ~ _ ~ LITERAL(value) ~ _ ~ exp ~ _  => StoreVariable(value, exp.toString)
            }
        }

        val following = {
            O_P ~ COLON ~ statement ~ statement ~ C_P ^^ {
                case _ ~ _ ~ s1 ~ s2 ~ _  => ExecuteStatement(s1, s2)
            }
        }

        val whileStatement = {
            O_P ~ WHILE_TOKEN ~ expression ~ statement ~ C_P ^^ {
                case _ ~ _ ~ exp ~ s ~ _ => WhileExecution(exp, s)
            }
        }

         whileStatement  | following | assignation

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
        print(WhileCompiler("(:= (var 1) (quote 4) )"))
        // print(WhileCompiler("(cons (var 5) (quote 4))"))

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