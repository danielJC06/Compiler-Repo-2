/*Tristan Lotivio*/
/*Project 5: TypeChecking.cpp*/
/* 4/7/2021 */
/* Dr. Zhijiang Dong */

#include <sstream>
#include "TypeChecking.h"
#include "Absyn.h"

namespace semantics
{
	//insert a variable into the var/function symbol table
	void TypeChecking::insertVar(string name, symbol::SymTabEntry entry)
	{
		string			msg;
		stringstream	ss(msg);

		if ( env.getVarEnv()->localContains(name) )
		{
			symbol::SymTabEntry		old = env.getVarEnv()->lookup(name);
			ss << "variable " << name << " is already defined at line " << old.node->getLineno();
			error(entry.node, ss.str());

		}
		else
			env.getVarEnv()->insert( name, entry );
	}

	//insert a function into the var/function symbol table
	void TypeChecking::insertFunc(string name, symbol::SymTabEntry entry)
	{
		string			msg;
		stringstream	ss(msg);

		if ( env.getVarEnv()->localContains(name) )
		{
			symbol::SymTabEntry		old = env.getVarEnv()->lookup(name);
			ss << "function " << name << " is already defined at line " << old.node->getLineno();
			error(entry.node, ss.str());

		}
		else
			env.getVarEnv()->insert( name, entry );
	}

	//insert a type into the type symbol table
	void TypeChecking::insertType(string name, symbol::SymTabEntry entry)
	{
		string			msg;
		stringstream	ss(msg);

		if ( env.getTypeEnv()->localContains(name) )
		{
			symbol::SymTabEntry		old = env.getTypeEnv()->lookup(name);
			ss << "variable " << name << " is already defined at line " << old.node->getLineno();
			error(entry.node, ss.str());

		}
		else
			env.getTypeEnv()->insert( name, entry );
	}

	const types::Type* TypeChecking::visit(const Absyn *v)
	{
		if ( dynamic_cast<const Exp *>(v) != NULL )
			return visit( dynamic_cast<const Exp *>(v) );
		else if ( dynamic_cast<const Var *>(v) != NULL )
			return visit( dynamic_cast<const Var *>(v) );
		else if ( dynamic_cast<const Dec *>(v) != NULL )
			return visit( dynamic_cast<const Dec *>(v) );
		else
			throw runtime_error("invalid node");
	}

	const types::Type* TypeChecking::visit(const Exp *e)
	{
		if (dynamic_cast<const OpExp*>(e) != NULL)			
			return visit((const OpExp*)e);
		else if (dynamic_cast<const VarExp*>(e) != NULL)	
			return visit((const VarExp*)e);
		else if (dynamic_cast<const NilExp*>(e) != NULL)	
			return visit((const NilExp*)e);
		else if (dynamic_cast<const IntExp*>(e) != NULL)	
			return visit((const IntExp*)e);
		else if (dynamic_cast<const StringExp*>(e) != NULL) 
			return visit((const StringExp*)e);
		else if (dynamic_cast<const CallExp*>(e) != NULL)	
			return visit((const CallExp*)e);
		else if (dynamic_cast<const SeqExp*>(e) != NULL)	
			return visit((const SeqExp*)e);
		else if (dynamic_cast<const AssignExp*>(e) != NULL) 
			return visit((const AssignExp*)e);
		else if (dynamic_cast<const IfExp*>(e) != NULL)		
			return visit((const IfExp*)e);
		else if (dynamic_cast<const WhileExp*>(e) != NULL)	
			return visit((const WhileExp*)e);
		else if (dynamic_cast<const ForExp*>(e) != NULL)	
			return visit((const ForExp*)e);
		else if (dynamic_cast<const BreakExp*>(e) != NULL)	
			return visit((const BreakExp*)e);
		else if (dynamic_cast<const LetExp*>(e) != NULL)	
			return visit((const LetExp*)e);
		else if (dynamic_cast<const ArrayExp*>(e) != NULL)	
			return visit((const ArrayExp*)e);
		else throw new runtime_error("TypeChecking.visit(Exp*)");
	}

	const types::Type* TypeChecking::visit(const Var *v)
	{
		if (dynamic_cast<const SimpleVar *>(v) != NULL)			
			return visit((const SimpleVar *) v);
		else if (dynamic_cast<const SubscriptVar *>(v) != NULL) 
			return visit((const SubscriptVar *)v);
		else throw new runtime_error("TypeChecking.visit(Var*)");
	}

	const types::Type* TypeChecking::visit(const Dec *d)
	{
		if (dynamic_cast<const TypeDec *>(d) != NULL)			
			return visit((const TypeDec *) d);
		else if (dynamic_cast<const VarDec *>(d) != NULL)		
			return visit((const VarDec *) d);
		else throw new runtime_error("TypeChecking.visit(Dec*)");
	}

	const types::Type* TypeChecking::visit(const Ty *t)
	{
		if (dynamic_cast<const NameTy *>(t) != NULL)			
			return visit((const NameTy *) t);
		else if (dynamic_cast<const ArrayTy *>(t) != NULL)		
			return visit((const ArrayTy *) t);
		else throw new runtime_error("TypeChecking.visit(Ty*)");
	}

	//functions checking semantic error of different type of Var nodes
	const types::Type* TypeChecking::visit(const SimpleVar *v)
	{
		/* check if the variable is defined by looking up the symbol table*/
		if (env.getVarEnv()->contains(v->getName())) {
			return env.getVarEnv()->lookup(v->getName()).info;
		}
		else {
			error(v, "undefined variable");
			return NULL;
		}
		
	}

	const types::Type* TypeChecking::visit(const SubscriptVar *v)
	{
		/* check both the variable and index */
		visit(v->getIndex());
		return visit(v->getVar());
	}


	//functions checking semantic error of different type of Exp nodes
	const types::Type* TypeChecking::visit(const OpExp *e)
	{
		/* check both operands */
		const types::Type* t1 = visit(e->getLeft());
		const types::Type* t2 = visit(e->getRight());

		if (t1 == t2) {
			return t1;
		}
		else {
			error(e, "undefined variable");
			return NULL;
		}

		
	}

	const types::Type* TypeChecking::visit(const VarExp *e)
	{
		/* check the variable */
		return visit(e->getVar());
	}

	const types::Type* TypeChecking::visit(const NilExp *e)
	{
		//don't need to do anything
		return NULL;
	}

	const types::Type* TypeChecking::visit(const IntExp *e)
	{
		//don't need to do anything
		return NULL;
	}

	const types::Type* TypeChecking::visit(const StringExp *e)
	{
		//don't need to do anything
		return NULL;
	}

	const types::Type* TypeChecking::visit(const CallExp *e)
	{
		/*
			step 1: check the function name
			step 2: check every argument expression
		*/
		string name = e->getFunc();
		if (env.getVarEnv()->contains(name)) {
			const types::Type* ptr = NULL;
			const ExpList* args = e->getArgs();
			while (args != NULL) {
				ptr = visit(args->getHead());
				args = args->getRest();
			}
			return ptr;
		}
		else {
			error(e, "Undefined function name.");
			return NULL;
		}
		
	}

	const types::Type* TypeChecking::visit(const SeqExp *e)
	{
		/*	check every expression in the sequence */
		const types::Type* ptr = NULL;
		const ExpList* exp = e->getList();
		while (exp != NULL) {
			ptr = visit(exp->getHead());
			exp = exp->getRest();
		}
		return ptr;
	}

	const types::Type* TypeChecking::visit(const AssignExp *e)
	{
		/* check both variable and expression */
		visit(e->getVar());
		return visit(e->getExp());
	} 

	const types::Type* TypeChecking::visit(const IfExp *e)
	{
		/* check test condition, then-clause, and else-clause (if exists) */
		const types::Type* test = visit(e->getTest());
		if (test != NULL) 
			return test;
		
		
		const types::Type* then = visit(e->getThenClause());
		if (then != NULL) 
			return then;
		
		
		const types::Type* elseE = visit(e->getElseClause());
		if (elseE != NULL) 
			return elseE;
		
		
		return NULL;
	}

	const types::Type* TypeChecking::visit(const WhileExp *e)
	{
		/* check both the test condition and loop-body expression */
		const types::Type* ptr = visit(e->getTest());
		if (ptr != NULL)
			return ptr;

		ptr = visit(e->getBody());
		if (ptr != NULL)
			return ptr;

		return NULL;
	}

	const types::Type* TypeChecking::visit(const ForExp *e)
	{
		/*
			step 1: begin a new scope for variable
			step 2: check var declaration, upper bound expression, and loop-body
			step 3: end the scope
		*/
		env.getVarEnv()->beginScope();

		visit(e->getVar());
		visit(e->getHi());
		visit(e->getBody());

		env.getVarEnv()->endScope();
		return NULL;
	}

	const types::Type* TypeChecking::visit(const BreakExp *e)
	{
		//don't need to do anything
		return NULL;
	}

	const types::Type* TypeChecking::visit(const LetExp *e)
	{
		/*
			step 1: begin a new scope for type and variable/function symbol tables
			step 2: check every declaraion in the decl list
			step 3: check the body expression
			step 4: end the scope for both symbol tables
		*/
		env.getVarEnv()->beginScope();
		env.getTypeEnv()->beginScope();

		const absyn::DecList* decs = e->getDecs();
		
		while (decs != NULL) {
			visit(decs->getHead());
			decs = decs->getRest();
		}

		visit(e->getBody());

		env.getVarEnv()->endScope();
		env.getTypeEnv()->endScope();

		return NULL;
	}

	const types::Type* TypeChecking::visit(const ArrayExp *e)
	{
		/*
			step 1: check the type of the array by looking up the type symbol table
			step 2: check the size expression
			step 3: check the initial expression
		*/
		
		if (env.getTypeEnv()->contains(e->getType())) {
			visit(e->getSize());
			return visit(e->getInit());
		}
		else {
			error(e, "undefined array");
			return NULL;
		}

		return NULL;
	}

	const types::Type* TypeChecking::visit(const VarDec *d)
	{
		/*
			step 1: insert the variable to the var/function symbol table
			step 2: if the type information is provided, check the type
			step 3: check the initial expression
		*/

		insertVar(d->getName(), symbol::SymTabEntry(env.getVarEnv()->getLevel(), NULL, d));

		if (d->getType() != NULL)
			visit(d->getType());

		return visit(d->getInit());

		
	}

	const types::Type* TypeChecking::visit(const TypeDec *d)
	{
		/*
			step 1: insert the name of the new type to the type symbol table
			step 2: check the type information of the new type
		*/

		insertType(d->getName(), symbol::SymTabEntry(env.getTypeEnv()->getLevel(), NULL, d));

		return visit(d->getTy());
	}

	//functions checking semantic error of different type of Ty nodes
	const types::Type* TypeChecking::visit(const NameTy *t)
	{
		/*
			step 1: check if the type name is defined by looking up the type symbol table
		*/
		string name = t->getName();
		if (env.getTypeEnv()->contains(name)) {
			return env.getTypeEnv()->lookup(name).info;
		}
		else {
			error(t, "undefined type");
			return NULL;
		}		
	}


	const types::Type* TypeChecking::visit(const ArrayTy *t)
	{
		/*
			step 1: Check the name of the array type by looking up the type symbol table
		*/
		string name = t->getName();
		if (env.getTypeEnv()->contains(name)) {
			return env.getTypeEnv()->lookup(name).info;
		}
		else {
			error(t, "undefined type");
			return NULL;
		}
		
	}


} // end of namespace semantics
