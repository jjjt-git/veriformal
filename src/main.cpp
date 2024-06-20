#include <iostream>
#include <sstream> 		//istringstream
#include <stack>
#include <fstream>
#include <string> 		//to_string, stoi
#include <algorithm>    // std::min


#include "basicfuns.h"
#include "translexp.h"
#include "transldecl.h"
#include "translca.h"
#include "translstm.h"
#include "translmodule.h"
#include "flattening.h"
#include "translgenerate.h"

using namespace std;

 
 
 /* NOTES:
  - operator precedence is not considered in epxressions. better use parenthsis. 
  - part select in expressions ONLY supports nat value, not variable
  - in declaration and left-hand side and delay of continuous assigns, parethesis are not supported
  - translexp function assume string without putting [] around operators. giving notation with [] will
     give termination error. TODO: debug;
  - Only single pair of outside parenthsis around a statement is supported. 
  - binary numbers are not supported 
  - nested blockes (e.g., nested if-then-else, while loop, ...) are not supported. 
  - forever, for, repeat, ... are not supported  
  //TODO: more than one parenthsis in sensitivity list?
  //TODO: renaming of variables in the submodule
  //TODO: nested instantiation is not supported;
  //TODO: only ordered ports are suppported in module instantiation 
 */
 
int main()
{	   
	string input; 				//formated input (.v file, with end of line replaced with ' ')
	string toplist; 			//body of module
	string ports;   			//port list of module
	string translatedbody; 		//translated module body (top list)
	string translatedmodule; 	//translated Verilog module 
	string HOLdefinition; 		//header for Isabelle/HOL definition
    string HOLlibraries;	
	string VerilogIds; 			//list of identifiers in Verilog module (to be converted to Isabelle/HOL names)
	
	string inputfile = "stallbuffer.v";  //input Verilog file
	
	//clear the contents of file 'inputfile.v' (stores list of names (as constructors))
	ofstream names;
	names.open ("names.txt");	//output text file, where all identifier names are stored, separated by |. 
	names <<"";
	names.close();
    	
	//erase comments if there are any and update changes in the file
	erasecommentsfile(inputfile);	
		
	//format input (replaces 'end of line' char with ' ' in Verilog .v file)
	//this is needed as translation functions use ' ' as delimiter between tokens. 
	input = formatinput(inputfile);		//gets input file name
	
	//replace module instances with the flattened sub-module as suggested by Gordon 
	input = flattening (input);
		
	ports = getports(input);   	 //port list of module
	toplist = gettoplist(input); //body of module
	
	
	toplist = translgenerate(toplist);   //translate generate statement in module body
	
	VerilogIds = translverilogids(toplist);  //create name definitions for Verilog ids and updates 'Syntax.thy' file
	cout<<"\nNames added to Syntax.thy file: "<<VerilogIds;

	
	//create preprocessed module (with generate statement resolved) and store in file 'preprocessed.v'
	ofstream myfile;
	myfile.open ("preprocessed.v");   //store the resulted Isabelle/HOL theory in output.thy file.
	myfile <<getmodulefirstline(input) + ";\n" + toplist + "\nendmodule";
	myfile.close();
	
	translatedbody = translmodule(toplist); //translated module body (top list)
	HOLlibraries = "theory translated \n imports Semantic Correctness \n begin \n\n";

	translatedmodule = "module ([" + ports + "])\n\n" + translatedbody + "\n\nendmod"; //translated Verilog module 
	HOLdefinition = "definition verimodule :: program where \n \"verimodule = \n";
	
	//write the translated Verilog program to 'output.thy' file
	myfile.open ("translated.thy");   //store the resulted Isabelle/HOL theory in output.thy file.
	myfile <<HOLlibraries + HOLdefinition + translatedmodule + "\n\"" + "\n end";
	myfile.close();
  
   return 0;
}

