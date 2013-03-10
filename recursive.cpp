#include <iostream>
using namespace std;

struct Zero {};

template<typename N>
struct Succ
{
	typedef N value;
};


template<typename T>
struct Show;

template<>
struct Show<Zero> {
	static std::string show() {
		return "Z";
	}
};

template<typename T>
struct Show<Succ<T> > {
	static std::string show() {
		return "S " + Show<T>::show();
	}
};

template<typename T1, typename T2>
struct Add;

template<typename T1>
struct Add<T1, Zero>
{
	typedef T1 result;
};

template<typename T1, typename T2>
struct Add<T1, Succ<T2> >
{
	typedef Succ<typename Add<T1, T2>::result> result;
};

int Z(int) {
	return 0;
}

int N(int x) {
	return x + 1;
}

template<int N>
int U1(int x1) {
	if (N == 1)
		return x1;
	else
		throw "ololo";
}

template<int N>
int U2(int x1, int x2) {
	if (N == 1)
		return x1;
	else if (N == 2)
		return x2;
	else
		throw "ololo";
}

template<int N>
int U3(int x1, int x2, int x3) {
	if (N == 1)
		return x1;
	else if (N == 2)
		return x2;
	else if (N == 3)
		return x3;
	else
		throw "ololo";
}	

template<int (*f)(int), int (*g1)(int)>
int S11(int x) {
	return f(g1(x));
}

template<int (*f)(int, int), int (*g1)(int), int (*g2)(int)>
int S21(int x) {
	return f(g1(x), g2(x));
}

template<int (*f)(int, int, int), int (*g1)(int), int (*g2)(int), int (*g3)(int)>
int S31(int x) {
	return f(g1(x), g2(x), g3(x));
}

template<int (*f)(int), int (*g1)(int, int, int)>
int S13(int x1, int x2, int x3) {
	return f(g1(x1, x2, x3));
}


template<int (*f)(int), int (*g)(int, int, int)>
int R1(int x1, int y) {
	if (y == 0)
		return f(x1);
	else
		return g(x1, y - 1, R1<f, g>(x1, y - 1));
}

// template<int (*f)(int x), int (*g1)(int x)>
// int S1(int x)
// {
// 	return f(g1(x));
// }

int main() {
	// std::cout << R1<U1<1>, S13<N, U3<3> > >(5, 3) << std::endl;
	// std::cout << S11<N, N>(3) << std::endl;
	//typedef Succ<Succ<Zero> > alala;
	typedef Zero Zero2;
	typedef Succ<Zero> One;
	typedef Succ<One> Two;
	typedef Succ<Two> Three;
	typedef typename Add<Three, Three>::result sum;
	std::cout << Show<sum>::show();
	//std::cout << U<1>(3, 2, 1);
}