package main.visitor.TypeChecker;

public class ErrorInType implements  Comparable<ErrorInType>{
    private String error;
    private int line;

    public ErrorInType(int line , String error) {
        this.line = line;
        this.error = error;
    }

    public int getLine() { return line; }
    public String getError()   {  return error; }

    @Override
    public int compareTo(ErrorInType err) {
        int line  =((ErrorInType)err).getLine();
        /* For Ascending order*/
        return this.line - line;
    }

    @Override
    public String toString() {
        return "Line:" + Integer.toString(this.line) + ":" + this.error;
    }

}
