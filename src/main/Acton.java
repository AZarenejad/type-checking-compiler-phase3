package main;

import main.ast.node.Program;
import main.compileError.CompileErrorException;
//import main.visitor.astPrinter.ASTPrinter;
import main.visitor.nameAnalyser.NameAnalyser;

import main.visitor.TypeChecker.TypeExtractor;
import org.antlr.v4.runtime.*;

//import org.antlr.v4.runtime.*;

import main.parsers.actonLexer;
import main.parsers.actonParser;

import java.io.IOException;

// Visit https://stackoverflow.com/questions/26451636/how-do-i-use-antlr-generated-parser-and-lexer
public class Acton {
    public static void main(String[] args) throws IOException {
        CharStream reader = CharStreams.fromFileName(args[1]);
        actonLexer lexer = new actonLexer(reader);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        actonParser parser = new actonParser(tokens);
        try{
            Program program = parser.program().p; // program is starting production rule
            NameAnalyser nameAnalyser = new NameAnalyser();
            nameAnalyser.visit(program);
            if( nameAnalyser.numOfErrors() > 0 )
                throw new CompileErrorException();
            TypeExtractor typeExtractor = new TypeExtractor();
            typeExtractor.visit(program);
        }
        catch(CompileErrorException compileError){
        }
    }
}