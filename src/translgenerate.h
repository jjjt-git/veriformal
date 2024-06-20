#ifndef TRANSLGENERATE_H_INCLUDED
#define TRANSLGENERATE_H_INCLUDED

using namespace std;  		//needed for string types

string translgenerate (string str);
string getgenvar (string str);
string getgenbody (string str);
string repeatgenbody (string str, string genvar, int genvarvalue);
string getgenindexedids (string genstm, string genvar, int genvarvalue);

string transformarrays (string str);
string repeatdeclaration (string str);
string translindexids(string module, string arrayids, string indexedids);
string getmodulefirstline(string module);
string getarrayids (string module);

#endif //TRANSLGENERATE_H_INCLUDED