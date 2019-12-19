package main.visitor.TypeChecker;

import main.ast.node.Main;
import main.ast.node.Program;
import main.ast.node.declaration.ActorDeclaration;
import main.ast.node.declaration.ActorInstantiation;
import main.ast.node.declaration.VarDeclaration;
import main.ast.node.declaration.handler.HandlerDeclaration;
import main.ast.node.declaration.handler.MsgHandlerDeclaration;
import main.ast.node.expression.*;
import main.ast.node.expression.operators.BinaryOperator;
import main.ast.node.expression.operators.UnaryOperator;
import main.ast.node.expression.values.BooleanValue;
import main.ast.node.expression.values.IntValue;
import main.ast.node.expression.values.StringValue;
import main.ast.node.statement.*;
import main.ast.type.Type;
import main.ast.type.actorType.ActorType;
import main.ast.type.arrayType.ArrayType;
import main.ast.type.noType.NoType;
import main.ast.type.primitiveType.BooleanType;
import main.ast.type.primitiveType.IntType;
import main.ast.type.primitiveType.StringType;
import main.symbolTable.*;
import main.symbolTable.itemException.ItemNotFoundException;
import main.symbolTable.symbolTableVariableItem.*;
import main.visitor.TypeChecker.ErrorInType;
import main.visitor.VisitorImpl;
import main.ast.node.expression.*;
import org.antlr.v4.codegen.model.decl.ContextRuleListIndexedGetterDecl;
import org.antlr.v4.gui.SystemFontMetrics;


import javax.print.DocFlavor;
import javax.print.attribute.standard.NumberOfDocuments;
import javax.sound.midi.SysexMessage;
import javax.swing.*;
import java.awt.desktop.ScreenSleepEvent;
import java.util.ArrayList;
import java.util.Collections;
import java.util.concurrent.atomic.AtomicBoolean;


public class TypeExtractor extends VisitorImpl {
    private SymbolTableActorItem curr_actor;
    private SymbolTableHandlerItem curr_handler;
    private SymbolTableMainItem curr_main;
    private ArrayList<ErrorInType> errors = new ArrayList<ErrorInType>();
    private boolean in_main = false;
    private boolean in_actor = false;
    private boolean in_handler = false;
    private boolean in_for = false;
    private boolean isInitHandler = false;
    private boolean in_known_actor = false;
    private boolean msg_handler_id = false;
    private boolean msg_handler_id_call = false;
    private boolean act_var_id = false;



    private Type type_getter_from_main(Identifier id) throws ItemNotFoundException {
        Type the_type = null;
        try {
            SymbolTableVariableItem init_item = (SymbolTableVariableItem) this.curr_main.getMainSymbolTable().get(
                    SymbolTableVariableItem.STARTKEY + id.getName());
            the_type = init_item.getVarDeclaration().getType();
        } catch (ItemNotFoundException e) {
            throw new ItemNotFoundException();
        }
        return the_type;
    }

    private Type type_getter_from_actor_items(Identifier id) throws ItemNotFoundException {
        Type the_type = null;
        try {
            SymbolTableActorItem actorItem = (SymbolTableActorItem) SymbolTable.root.get(
                    SymbolTableActorItem.STARTKEY + id.getName());

            if (actorItem.getActorDeclaration().getName().getType() instanceof NoType)
                the_type = new NoType();
            else
                the_type = new ActorType(id);
        } catch (ItemNotFoundException e) {
            throw new ItemNotFoundException();
        }
        return the_type;
    }

    private Type type_getter_from_whole_actor(Identifier id) throws ItemNotFoundException {
        Type the_type = null;
        try {
            the_type = this.type_getter_from_handler(id);
        } catch (ItemNotFoundException e) {
            try {
                the_type = this.type_getter_from_act(id);
            } catch (ItemNotFoundException e1) {
                throw new ItemNotFoundException();
            }
        }
        return the_type;
    }

    private Type type_getter_from_handler(Identifier id) throws ItemNotFoundException {
        Type the_type = null;
        try {
            SymbolTableVariableItem init_item = (SymbolTableVariableItem) this.curr_handler.getHandlerSymbolTable().get(
                    SymbolTableVariableItem.STARTKEY + id.getName());
            the_type = init_item.getVarDeclaration().getType();
        } catch (Exception e) {
            throw new ItemNotFoundException();
        }
        return the_type;
    }

    private Type type_getter_from_act(Identifier id) throws ItemNotFoundException {
        Type the_type = null;
        try {
            SymbolTableVariableItem init_item = (SymbolTableVariableItem) this.curr_actor.getActorSymbolTable().get(
                    SymbolTableVariableItem.STARTKEY + id.getName());
            the_type = init_item.getVarDeclaration().getType();
        } catch (ItemNotFoundException e) {
            throw new ItemNotFoundException();
        }
        return the_type;
    }

    private ArrayList<VarDeclaration> get_known_actors_from_actor(Identifier actor) {
        ArrayList<VarDeclaration> the_known_actors = null;
        try {
            SymbolTableActorItem actorItem = (SymbolTableActorItem) SymbolTable.root.get(
                    SymbolTableActorItem.STARTKEY + actor.getName()
            );
            the_known_actors = actorItem.getActorDeclaration().getKnownActors();
        } catch (ItemNotFoundException e) {
            System.out.printf("There is no such %s", actor.getName());
        }
        return the_known_actors;
    }

    private Type type_getter(Identifier id) {
        Type the_type = null;
        try {
            the_type = this.type_getter_from_whole_actor(id);
        } catch (ItemNotFoundException e) {
            try {
                the_type = this.type_getter_from_main(id);
            } catch (ItemNotFoundException e1) {
                try {
                    the_type = this.type_getter_from_actor_items(id);
                } catch (ItemNotFoundException e2) {
                    the_type = new NoType();
                }
            }
        }
        return the_type;
    }

    private boolean check_first_actor_subtype_second(String act1, String ac2) {
        boolean ret = false;
        if (act1.equals("notype")) {
            ret = true;
            return ret;
        }
        SymbolTableActorItem act1_sym = null;
        try {
            act1_sym = ((SymbolTableActorItem) SymbolTable.root.get(SymbolTableActorItem.STARTKEY +
                    act1));
            SymbolTableActorItem act2_sym = ((SymbolTableActorItem) SymbolTable.root.get(SymbolTableActorItem.STARTKEY + ac2));

            if (act1_sym.getActorDeclaration().getName().equals(act2_sym.getActorDeclaration().getName())) {
                ret = true;
                return ret;
            }
            while (act1_sym.getParentName() != null) {
                if (act1_sym.getParentName().equals(act2_sym.getActorSymbolTable().getName())) {
                    ret = true;
                    break;
                } else {
                    act1_sym = ((SymbolTableActorItem) SymbolTable.root.get(SymbolTableActorItem.STARTKEY +
                            act1_sym.getParentName()));
                }
            }
        } catch (ItemNotFoundException e) {
            ret = false;
            return ret;
        }
        return ret;
    }


    public void print_type_errors() {
        Collections.sort(errors);
        for (ErrorInType str : errors) {
            System.out.println(str);
        }
    }

    private boolean isLeftValue(Expression expression) {
        return (expression instanceof ArrayCall || expression instanceof Identifier ||
                expression instanceof ActorVarAccess);
    }


    @Override
    public void visit(Program program) {
        //TODO: implement appropriate visit functionality
        for (ActorDeclaration actorDeclaration : program.getActors()) {
            actorDeclaration.accept(this);
        }
        program.getMain().accept(this);
        print_type_errors();

    }

    @Override
    public void visit(ActorDeclaration actorDeclaration) {
        //TODO: implement appropriate visit functionality
        String actor_name = actorDeclaration.getName().getName();
        visitExpr(actorDeclaration.getName());
        visitExpr(actorDeclaration.getParentName());
        SymbolTableActorItem parent_sym;

//        if (actorDeclaration.getParentName()!=null) {
//            String parent_name = actorDeclaration.getParentName().getName();
//            try {
//                parent_sym = (SymbolTableActorItem) SymbolTable.root.get(SymbolTableActorItem.STARTKEY + parent_name);
//            } catch (ItemNotFoundException ignored) {
//                int line = actorDeclaration.getParentName().getLine();
//                String err = "actor " + parent_name + " is not declared";
//                errors.add(new ErrorInType(line, err));
//            }
//        }
        try {
            this.curr_actor = (SymbolTableActorItem) SymbolTable.root.get(SymbolTableActorItem.STARTKEY + actor_name);
            this.in_actor = true;
        } catch (ItemNotFoundException ignored) {
        }

        for (VarDeclaration varDeclaration : actorDeclaration.getKnownActors()) {
            varDeclaration.accept(this);
            String actor_name_as_type_in_known_actor_part = varDeclaration.getType().toString();
            SymbolTableActorItem act_sym = null;
            try {
                act_sym = (SymbolTableActorItem) SymbolTable.root.get(SymbolTableActorItem.STARTKEY +
                        actor_name_as_type_in_known_actor_part);
            } catch (ItemNotFoundException e) {
                int line = varDeclaration.getIdentifier().getLine();
                String err = "actor " + actor_name_as_type_in_known_actor_part + " is not declared";
                errors.add(new ErrorInType(line, err));
                varDeclaration.getIdentifier().setType(new NoType());
                varDeclaration.setType(new NoType());
            }
        }


        for (VarDeclaration varDeclaration : actorDeclaration.getActorVars()) {
            varDeclaration.accept(this);
        }

        if (actorDeclaration.getInitHandler() != null) {
            this.isInitHandler = true;
            actorDeclaration.getInitHandler().accept(this);
            this.isInitHandler = false;
        }

        for (MsgHandlerDeclaration msgHandlerDeclaration : actorDeclaration.getMsgHandlers()) {
            msgHandlerDeclaration.accept(this);
        }
        this.in_actor = false;
    }

    @Override
    public void visit(HandlerDeclaration handlerDeclaration) {
        String handler_name = handlerDeclaration.getName().getName();
        msg_handler_id = true;
        visitExpr(handlerDeclaration.getName());
        msg_handler_id = false;
        try {
            this.curr_handler = (SymbolTableHandlerItem) this.curr_actor.getActorSymbolTable().get(SymbolTableHandlerItem.STARTKEY + handler_name);
            this.in_handler = true;
        } catch (ItemNotFoundException ignored) {

        }

        for (VarDeclaration argDeclaration : handlerDeclaration.getArgs())
            argDeclaration.accept(this);
        for (VarDeclaration localVariable : handlerDeclaration.getLocalVars())
            localVariable.accept(this);
        for (Statement statement : handlerDeclaration.getBody()) {
            visitStatement(statement);
        }
        this.in_handler = false;
    }

    @Override
    public void visit(VarDeclaration varDeclaration) {
        //TODO: implement appropriate visit functionality
        visitExpr(varDeclaration.getIdentifier());
    }

    @Override
    public void visit(Main mainActors) {
        //TODO: implement appropriate visit functionality
        if (mainActors == null)
            return;

        try {
            this.curr_main = (SymbolTableMainItem) SymbolTable.root.get(SymbolTableMainItem.STARTKEY + "main");
            this.in_main = true;
        } catch (ItemNotFoundException ignored) {

        }

        for (ActorInstantiation mainActor : mainActors.getMainActors())
            mainActor.accept(this);
        this.in_main = false;

    }


    @Override
    public void visit(ActorInstantiation actorInstantiation) {
        //TODO: implement appropriate visit functionality
        if (actorInstantiation == null)
            return;
        visitExpr(actorInstantiation.getIdentifier());
        // maybe here we should check whether or not actor typr declare in root *****************



        int known_pass = 0;
        for (Identifier knownActor : actorInstantiation.getKnownActors()) {
            //  maybe here we should check that an identifier declare in main *****************
            visitExpr(knownActor);
            known_pass += 1;
        }
        int arg_pass = 0;
        for (Expression initArg : actorInstantiation.getInitArgs()) {
            visitExpr(initArg);
            arg_pass += 1;
        }


        SymbolTableActorItem act_sym = null;
        ArrayList<VarDeclaration> known_act = null;
        ArrayList<VarDeclaration> init_args = null;
        int actial_init_arg_size = 0;
        try {
            act_sym = ((SymbolTableActorItem) SymbolTable.root.get(SymbolTableActorItem.STARTKEY +
                    actorInstantiation.getIdentifier().getType().toString()));
            known_act = act_sym.getActorDeclaration().getKnownActors();

            if (act_sym.getActorDeclaration().getInitHandler() != null) {
                init_args = act_sym.getActorDeclaration().getInitHandler().getArgs();
                actial_init_arg_size = init_args.size();
            }

            if (known_act.size() != known_pass) {
                int line = actorInstantiation.getLine();
                String err = "knownactors do not match with definition";
                errors.add(new ErrorInType(line, err));
                return;
            }
            int i = 0;
            for (Identifier knownActor : actorInstantiation.getKnownActors()) {
                String act1 = knownActor.getType().toString();
                String act2 = known_act.get(i).getType().toString();
//                System.out.printf(" %d: %s ---> %s\n " ,actorInstantiation.getLine(), act1,act2);
                if (!check_first_actor_subtype_second(act1, act2)) {
                    int line = actorInstantiation.getLine();
                    String err = "knownactors doe not match with definition";
                    errors.add(new ErrorInType(line, err));
                    return;
                }
                i+=1;
            }

            if (actial_init_arg_size != arg_pass) {
                int line = actorInstantiation.getLine();
                String err = "arguments do not match with definition";
                errors.add(new ErrorInType(line, err));
                return;
            }
            i = 0;

            for (Expression arg : actorInstantiation.getInitArgs()) {
                Type arg_init = init_args.get(i).getType();
                if (arg.getType() instanceof NoType) {
                    continue;
                } else {
                    if (!(arg.getType() instanceof IntType && arg_init instanceof IntType) ||
                            (arg.getType() instanceof StringType && arg_init instanceof StringType) ||
                            (arg.getType() instanceof ArrayType && arg_init instanceof ArrayType) ||
                            (arg_init instanceof BooleanType && arg_init instanceof BooleanType)) {
                        int line = actorInstantiation.getLine();
                        String err = "initial args does not match with definition";
                        errors.add(new ErrorInType(line, err));
                        return;
                    }
                }
            }


        } catch (ItemNotFoundException ignored) {
        }


    }


    @Override
    public void visit(UnaryExpression unaryExpression) {
        if (unaryExpression == null)
            return;

        Expression exp = unaryExpression.getOperand();
        UnaryOperator unaryOperator = unaryExpression.getUnaryOperator();
        visitExpr(exp);
        System.out.println(exp.toString());
        System.out.println(exp.getType());

        if (this.isLeftValue(exp)) {
            if (exp.getType() instanceof NoType) {
                unaryExpression.setType(new NoType());
            } else if ((unaryOperator.equals(UnaryOperator.minus)) && (exp.getType() instanceof IntType)) {
                unaryExpression.setType(new IntType());
            } else if ((unaryOperator.equals(UnaryOperator.not)) && (exp.getType() instanceof BooleanType)) {
                unaryExpression.setType(new BooleanType());
            } else if ((unaryOperator.equals(UnaryOperator.postinc)) && (exp.getType() instanceof IntType)) {
                unaryExpression.setType(new IntType());
            } else if ((unaryOperator.equals(UnaryOperator.postdec)) && (exp.getType() instanceof IntType)) {
                unaryExpression.setType(new IntType());
            } else if ((unaryOperator.equals(UnaryOperator.predec)) && (exp.getType() instanceof IntType)) {
                unaryExpression.setType(new IntType());
            } else if ((unaryOperator.equals(UnaryOperator.preinc)) && (exp.getType() instanceof IntType)) {
                unaryExpression.setType(new IntType());
            } else {
                unaryExpression.setType(new NoType());
                int line = unaryExpression.getLine();
                String err = "unsupported operand type for " + unaryOperator.name();
                errors.add(new ErrorInType(line, err));
            }
        } else {
            unaryExpression.setType(new NoType());
            int line = unaryExpression.getLine();
            String err;
            if (unaryOperator.equals(UnaryOperator.preinc) || unaryOperator.equals(UnaryOperator.postinc)) {
                err = "lvalue required as increment operand";
                errors.add(new ErrorInType(line, err));
            } else if (unaryOperator.equals(UnaryOperator.predec) || unaryOperator.equals(UnaryOperator.postdec)) {
                err = "lvalue required as decrement operand";
                errors.add(new ErrorInType(line, err));
            }
        }
    }

    @Override
    public void visit(BinaryExpression binaryExpression) {
        if (binaryExpression == null)
            return;


        Expression left_exp = binaryExpression.getLeft();
        Expression right_exp = binaryExpression.getRight();
        visitExpr(left_exp);
        visitExpr(right_exp);
        BinaryOperator binaryOperator = binaryExpression.getBinaryOperator();


        // operator add   sub  mult  div   mod
        if (binaryOperator.equals(BinaryOperator.add) || binaryOperator.equals(BinaryOperator.sub) ||
                binaryOperator.equals(BinaryOperator.mult) || binaryOperator.equals(BinaryOperator.div) ||
                binaryOperator.equals(BinaryOperator.mod)) {
            if ((left_exp.getType() instanceof IntType || left_exp.getType() instanceof NoType) &&
                    (right_exp.getType() instanceof IntType || right_exp.getType() instanceof NoType)) {
                binaryExpression.setType(new IntType());
            }
            else {
                int line = binaryExpression.getLine();
                String err = "unsupported operand type for " + binaryOperator.name();
                errors.add(new ErrorInType(line, err));
                binaryExpression.setType(new NoType());
            }
        }

        // operator less than   greater than
        else if (binaryOperator.equals(BinaryOperator.lt) || binaryOperator.equals(BinaryOperator.gt)) {
            if ((left_exp.getType() instanceof IntType || left_exp.getType() instanceof NoType) &&
                    (right_exp.getType() instanceof IntType || right_exp.getType() instanceof NoType)) {
                binaryExpression.setType(new BooleanType());
            }
            else {
                int line = binaryExpression.getLine();
                String err = "unsupported operand type for " + binaryOperator.name();
                errors.add(new ErrorInType(line, err));
                binaryExpression.setType(new NoType());
            }
        }


        // operator and or
        else if (binaryOperator.equals(BinaryOperator.and) ||  binaryOperator.equals(BinaryOperator.or)) {
            if ((left_exp.getType() instanceof BooleanType || left_exp.getType() instanceof NoType) &&
                    (right_exp.getType() instanceof BooleanType || right_exp.getType() instanceof NoType)) {
                binaryExpression.setType(new BooleanType());
            }
            else {
                int line = binaryExpression.getLine();
                String err = "unsupported operand type for " + binaryOperator.name();
                errors.add(new ErrorInType(line, err));
                binaryExpression.setType(new NoType());
            }
        }

        //operator == !=
        else if (binaryOperator.equals(BinaryOperator.eq) || binaryOperator.equals(BinaryOperator.neq)) {
            if ((left_exp.getType() instanceof IntType || left_exp.getType() instanceof NoType) &&
                    (right_exp.getType() instanceof IntType || right_exp.getType() instanceof NoType)) {
                binaryExpression.setType(new BooleanType());
            }
            else if ((left_exp.getType() instanceof BooleanType || left_exp.getType() instanceof NoType) &&
                    (right_exp.getType() instanceof BooleanType || right_exp.getType() instanceof NoType)) {
                binaryExpression.setType(new BooleanType());
            }
            else if ((left_exp.getType() instanceof StringType || left_exp.getType() instanceof NoType) &&
                    (right_exp.getType() instanceof StringType || right_exp.getType() instanceof NoType)) {
                binaryExpression.setType(new BooleanType());
            }
            else if ((left_exp.getType() instanceof ArrayType || left_exp.getType() instanceof NoType) &&
                    (right_exp.getType() instanceof ArrayType || right_exp.getType() instanceof NoType)) {
                if (left_exp.getType() instanceof NoType || right_exp.getType() instanceof NoType) {
                    binaryExpression.setType(new BooleanType());
                }
                else {
                    int size_left = ((ArrayType) left_exp.getType()).getSize();
                    int size_right = ((ArrayType) right_exp.getType()).getSize();
                    if (size_left == size_right) {
                        binaryExpression.setType(new BooleanType());
                    }
                    else {
                        int line = binaryExpression.getLine();
                        String err = "unsupported operand type for " + binaryOperator.name();
                        errors.add(new ErrorInType(line, err));
                        binaryExpression.setType(new NoType());
                    }
                }
            }
            else if ((left_exp.getType() instanceof ActorType || left_exp.getType() instanceof NoType) &&
                    (right_exp.getType() instanceof ActorType || right_exp.getType() instanceof NoType)) {
                if (left_exp.getType() instanceof NoType || right_exp.getType() instanceof NoType) {
                    binaryExpression.setType(new BooleanType());
                }
                else {
                    if (!left_exp.getType().toString().equals(right_exp.getType().toString())) {
                        int line = binaryExpression.getLine();
                        String err = "unsupported operand type for " + binaryOperator.name();
                        errors.add(new ErrorInType(line, err));
                        binaryExpression.setType(new NoType());
                    }
                }
            }
        }
//        // = aasign
//        else if(binaryExpression.equals(BinaryOperator.assign)){
//            if((left_exp.getType() instanceof IntType || left_exp.getType() instanceof NoType) &&
//                    (right_exp.getType() instanceof IntType || right_exp.getType() instanceof NoType)){
//                binaryExpression.setType(new IntType());
//            }
//            else if((left_exp.getType() instanceof StringType || right_exp.getType() instanceof NoType)&&
//                    (right_exp.getType() instanceof StringType || right_exp.getType() instanceof NoType)){
//                binaryExpression.setType(new StringType());
//            }
//            else if((left_exp.getType() instanceof BooleanType || left_exp.getType() instanceof  NoType)&&
//                    (right_exp.getType() instanceof BooleanType || left_exp.getType() instanceof NoType)){
//                binaryExpression.setType(new BooleanType());
//            }
//            else if ((left_exp.getType() instanceof ArrayType || left_exp.getType() instanceof NoType) &&
//                    (right_exp.getType() instanceof ArrayType || right_exp.getType() instanceof NoType)) {
//                if (left_exp.getType() instanceof NoType || right_exp.getType() instanceof NoType) {
//                    binaryExpression.setType(new NoType());
//                }
//                else {
//                    int size_left = ((ArrayType) left_exp.getType()).getSize();
//                    int size_right = ((ArrayType) right_exp.getType()).getSize();
//                    if (size_left == size_right) {
//                        binaryExpression.setType(new ArrayType(((ArrayType) binaryExpression.getLeft().getType()).getSize()));
//                    }
//                    else {
//                        int line = binaryExpression.getLine();
//                        String err = "operation assign requires equal array sizes" ;
//                        errors.add(new ErrorInType(line, err));
//                        binaryExpression.setType(new NoType());
//                    }
//                }
//            }
//            else{
//                int line = binaryExpression.getLine();
//                String err = "unsupported operand type for " + binaryOperator.name();
//                errors.add(new ErrorInType(line, err));
//                binaryExpression.setType(new NoType());
//            }
//        }


        if (left_exp.getType() instanceof NoType || right_exp.getType() instanceof NoType){
            binaryExpression.setType(new NoType());
        }
    }






    @Override
    public void visit(ArrayCall arrayCall) {
        visitExpr(arrayCall.getArrayInstance());
        visitExpr(arrayCall.getIndex());
        if (arrayCall.getArrayInstance().getType() instanceof NoType
                || arrayCall.getIndex().getType() instanceof NoType) {
            arrayCall.setType(new NoType());
        }
        else if ( !(arrayCall.getIndex().getType() instanceof IntType) ) {
            arrayCall.setType(new NoType());
            int line = arrayCall.getLine();
            String err ="Array index must be Integer type";
            errors.add(new ErrorInType(line,err));
        }
        else if ( !(arrayCall.getArrayInstance().getType() instanceof ArrayType) ) {
            arrayCall.setType(new NoType());
            int line = arrayCall.getLine();
            String err = "Array instance must be Array type";
            errors.add(new ErrorInType(line,err));
        }
        else
            arrayCall.setType(new IntType());
    }


    @Override
    public void visit(ActorVarAccess actorVarAccess) {
        if (actorVarAccess == null)
            return;
        if (in_main){
            act_var_id = true;
        }
        visitExpr(actorVarAccess.getVariable());
        act_var_id = false;
        actorVarAccess.setType(actorVarAccess.getVariable().getType());
        if (!in_actor){
            int line = actorVarAccess.getLine();
            String err = "self doesn't refer to any actor";
            errors.add(new ErrorInType(line,err));
            actorVarAccess.setType(new NoType());

        };

    }

    @Override
    public void visit(Identifier identifier) {
        if (identifier == null)
            return;
        if(!msg_handler_id && !msg_handler_id_call && !act_var_id) {
            if (this.in_main) {
                Type the_type = null;
                try {
                    the_type = this.type_getter_from_main(identifier);
//                System.out.printf("%s ------> %s\n",identifier.getName(),the_type.toString());
                    try {
                        Identifier temp_id = new Identifier(the_type.toString());
                        Type temp_type = this.type_getter_from_actor_items(temp_id);
//                    System.out.printf("%s ------> %s\n",temp_id.getName(),temp_type.toString());
                    } catch (ItemNotFoundException e1) {
                        int line = identifier.getLine();
                        String err = "actor " + the_type.toString() + " is not declared";
                        the_type = new NoType();
                        errors.add(new ErrorInType(line, err));
                        the_type = new NoType();
                    }
                } catch (ItemNotFoundException e) {
                    int line = identifier.getLine();
                    String err = "variable " + identifier.getName() + " is not declared";
                    the_type = new NoType();
                    errors.add(new ErrorInType(line, err));
                }
                identifier.setType(the_type);
//            System.out.printf("In the main : %s ===> %s\n", identifier.getName(), identifier.getType());
            } else if (this.in_actor) {
                Type the_type = null;
                if (this.in_handler) {
                    try {
                        the_type = this.type_getter_from_whole_actor(identifier);
                    } catch (ItemNotFoundException e1) {
                        int line = identifier.getLine();
                        String err = "variable " + identifier.getName() + " is not declared";
                        errors.add(new ErrorInType(line, err));
                        the_type = new NoType();
                    }
                } else {
                    try {
                        the_type = this.type_getter_from_act(identifier);
                    } catch (ItemNotFoundException e2) {
                        int line = identifier.getLine();
                        String err = new String("varibale " + identifier.getName() + " is not declared");
                        errors.add(new ErrorInType(line, err));
                        the_type = new NoType();
                    }
                }
                identifier.setType(the_type);
//            System.out.printf("In the actor : %s ===> %s\n", identifier.getName(), identifier.getType());
            } else {
                Type the_type = null;
                try {
                    the_type = this.type_getter_from_actor_items(identifier);
                } catch (ItemNotFoundException e3) {
                    int line = identifier.getLine();
                    String err = "actor " + identifier.getName() + " is not declared";
                    errors.add(new ErrorInType(line, err));
                    the_type = new NoType();
                }
                identifier.setType(the_type);
//            System.out.printf("In the decs : %s ===> %s\n", identifier.getName(), identifier.getType());
            }
        }


    }




    @Override
    public void visit(Self self) {
//        if (!in_actor){
//            int line = self.getLine();
//            String err = "self doesn't refer to any actor";
//            errors.add(new ErrorInType(line,err));
//            self.setType(new NoType());
//        }
    }

    @Override
    public void visit(Sender sender) {
        if (isInitHandler){
            int line = sender.getLine();
            String err = "no sender in initial msghander";
            errors.add(new ErrorInType(line, err));
        }

    }

    @Override
    public void visit(BooleanValue value) {
        value.setType(new BooleanType());
    }

    @Override
    public void visit(IntValue value) {
        value.setType(new IntType());
    }

    @Override
    public void visit(StringValue value) {
        value.setType(new StringType());

    }


    @Override
    public void visit(Block block) {
        if (block == null)
            return;
        for (Statement statement : block.getStatements())
            visitStatement(statement);
    }

    @Override
    public void visit(Conditional conditional) {
        visitExpr(conditional.getExpression());
        Expression cond = conditional.getExpression();
        if (cond!=null){
            if(!(cond.getType() instanceof NoType) || !(cond.getType() instanceof BooleanType)) {
                int line = conditional.getLine();
                String err = "condition type must be boolean";
                errors.add(new ErrorInType(line, err));
            }
        }
        visitStatement(conditional.getThenBody());
        visitStatement(conditional.getElseBody());
    }

    @Override
    public void visit(For loop) {
        in_for = true;
        visitStatement(loop.getInitialize());
        visitExpr(loop.getCondition());
        Expression cond = loop.getCondition();
        if (cond!= null){
            if (!(cond.getType() instanceof BooleanType || cond.getType() instanceof  NoType)) {
                int line = loop.getLine();
                String err = "condition type must be boolean";
                errors.add(new ErrorInType(line, err));
                cond.setType(new NoType());
            }
        }
        visitStatement(loop.getUpdate());
        visitStatement(loop.getBody());
        in_for = false;
    }

    @Override
    public void visit(Break breakLoop) {
        if(!in_for){
            int line = breakLoop.getLine();
            String err = "break statement not within loop";
            errors.add(new ErrorInType(line,err));
        }
    }

    @Override
    public void visit(Continue continueLoop) {
        if(!in_for){
            int line = continueLoop.getLine();
            String err = "continue statement not within loop";
            errors.add(new ErrorInType(line,err));
        }
    }

    @Override
    public void visit(MsgHandlerCall msgHandlerCall) {
        //TODO: implement appropriate visit functionality
        if (msgHandlerCall == null) {
            return;
        }
        int size_arg_pass = 0 ;
        try {
            visitExpr(msgHandlerCall.getInstance());
            msg_handler_id_call = true;
            visitExpr(msgHandlerCall.getMsgHandlerName());
            msg_handler_id_call = false;


            for (Expression argument : msgHandlerCall.getArgs()) {
                size_arg_pass+=1;
                visitExpr(argument);
            }
            SymbolTableActorItem the_actor = null;
            String actor_call_name ;
            if (msgHandlerCall.getInstance() instanceof Self){
                actor_call_name = curr_actor.getActorDeclaration().getName().getName();
            }
            else {
                actor_call_name = ((Identifier) msgHandlerCall.getInstance()).getType().toString();
            }
            try {
                the_actor =(SymbolTableActorItem)SymbolTable.root.get(SymbolTableActorItem.STARTKEY +
                        actor_call_name);
            } catch (ItemNotFoundException e1) {
                String name = ((Identifier)msgHandlerCall.getInstance()).getName();
                int line = msgHandlerCall.getLine();
                String err = "varibale " + name + " is not collable";
                errors.add(new ErrorInType(line,err));
            }
            SymbolTableHandlerItem the_handler = null;
            String handler_name = msgHandlerCall.getMsgHandlerName().getName();
            try {
                the_handler = (SymbolTableHandlerItem)the_actor.getActorSymbolTable().get(SymbolTableHandlerItem.STARTKEY +
                        handler_name);
            } catch (ItemNotFoundException e2) {
                int line = msgHandlerCall.getLine();
                String err = "there is no msghandler named " + handler_name + " in actor " + actor_call_name;
                errors.add(new ErrorInType(line,err));
            }
            ArrayList<VarDeclaration> arg_handler = null;
            arg_handler = the_handler.getHandlerDeclaration().getArgs();
            int arg_handler_size = 0;
            if (arg_handler!=null){
                arg_handler_size = arg_handler.size();
            }
            if (size_arg_pass != arg_handler_size){
                int line = msgHandlerCall.getLine();
                String err ="arguments do not match with definition";
                errors.add(new ErrorInType(line,err));
                return;
            }
            int i = 0;
            for (Expression argument : msgHandlerCall.getArgs()) {
                Type arg_pass = argument.getType();
                Type arg = (arg_handler.get(i)).getType();
                if (arg instanceof IntType){
                    if (!(arg_pass instanceof  IntType || arg_pass instanceof NoType)){
                        int line = msgHandlerCall.getLine();
                        String err ="arguments do not match with definition";
                        errors.add(new ErrorInType(line,err));
                        break;
                    }
                }
                else if (arg instanceof StringType){
                    if (!(arg_pass instanceof  StringType || arg_pass instanceof NoType)){
                        int line = msgHandlerCall.getLine();
                        String err ="arguments do not match with definition";
                        errors.add(new ErrorInType(line,err));
                        break;
                    }
                }
                else if (arg instanceof BooleanType){
                    if (!(arg_pass instanceof  BooleanType || arg_pass instanceof NoType)){
                        int line = msgHandlerCall.getLine();
                        String err ="arguments do not match with definition";
                        errors.add(new ErrorInType(line,err));
                        break;
                    }
                }
                else if (arg instanceof ArrayType){
                    if (!(arg_pass instanceof  ArrayType || arg_pass instanceof NoType)){
                        int line = msgHandlerCall.getLine();
                        String err ="arguments do not match with definition";
                        errors.add(new ErrorInType(line,err));
                        break;
                    }
                }
            }
        } catch (NullPointerException npe) {
//            System.out.println("null pointer exception occurred");
        }
    }

    @Override
    public void visit(Print print) {
        if (print == null)
            return;
        Expression print_arg = print.getArg();
        visitExpr(print_arg);
        if (!(print_arg.getType() instanceof NoType || print_arg.getType() instanceof IntType ||
                print_arg.getType() instanceof  StringType || print_arg.getType() instanceof BooleanType) ||
                print_arg.getType() instanceof ArrayType){
            int line = print.getLine();
            String err ="unsupported type for print";
            errors.add(new ErrorInType(line,err));
        }
    }


    @Override
    public void visit(Assign assign) {
        Expression left_value = assign.getlValue();
        Expression right_value = assign.getrValue();
        visitExpr(left_value);
        visitExpr(right_value);
        if (left_value instanceof ActorVarAccess){
            left_value = ((ActorVarAccess)left_value).getVariable();
        }
        if (!this.isLeftValue(left_value)){
            int line = assign.getLine();
            String err ="left side of assignment must be a valid lvalue";
            errors.add(new ErrorInType(line,err));
        }
        else if(left_value.getType() instanceof  IntType){
            if (!(right_value.getType() instanceof IntType || right_value.getType() instanceof NoType)){
                int line = assign.getLine();
                String err ="unsupported operand type for " + assign.toString();
                errors.add(new ErrorInType(line,err));
            }
        }
        else if(left_value.getType() instanceof  StringType){
            if (!(right_value.getType() instanceof StringType || right_value.getType() instanceof NoType)){
                int line = assign.getLine();
                String err ="unsupported operand type for " + assign.toString();
                errors.add(new ErrorInType(line,err));
            }
        }

        else if(left_value.getType() instanceof  BooleanType){
            if (!(right_value.getType() instanceof BooleanType || right_value.getType() instanceof NoType)){
                int line = assign.getLine();
                String err ="unsupported operand type for " + assign.toString();
                errors.add(new ErrorInType(line,err));
            }
        }
        else if(left_value.getType() instanceof ArrayType){
            if(!(right_value.getType() instanceof NoType)){
                if(right_value.getType() instanceof ArrayType){
                    int size1 = ((ArrayType)left_value.getType()).getSize();
                    int size2 = ((ArrayType)right_value.getType()).getSize();
                    if(size1!=size2){
                        int line = assign.getLine();
                        String err = "operation assign requires equal array sizes";
                        errors.add(new ErrorInType(line, err));
                    }
                }
                else {
                    int line = assign.getLine();
                    String err = "unsupported operand type for " + assign.toString();
                    errors.add(new ErrorInType(line, err));
                }
            }
        }
        else if(left_value.getType() instanceof ActorType){
            if (!(right_value.getType() instanceof  NoType)){
                if (!check_first_actor_subtype_second(right_value.getType().toString() , left_value.getType().toString())){
                    int line = assign.getLine();
                    String err = "unsupported operand type for " + assign.toString();
                    errors.add(new ErrorInType(line,err));
                }
            }
        }
    }

}



