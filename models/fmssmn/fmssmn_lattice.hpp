#ifndef fmssmn_lattice_hpp
#define fmssmn_lattice_hpp


#include "fmssmn.hpp"
#include "lattice_model.hpp"

namespace flexiblesusy {

class Lattice;

template<>
class Fmssmn<Lattice>: public Lattice_model {
public:
    Fmssmn();
    virtual ~Fmssmn() {}
    virtual void calculate_spectrum();
    virtual std::string name() const { return "FMSSMN"; }
    virtual void print(std::ostream& s) const;

    void  dx(Real a, const Eigen::VectorXd& x, Eigen::VectorXd& dx,
	     size_t nloops) const;
    void ddx(Real a, const Eigen::VectorXd& x, Eigen::MatrixXd& ddx,
	     size_t nloops) const;

    struct Translator : public Lattice_translator {
	Translator(RGFlow<Lattice> *f, size_t T, size_t m) :
	    Lattice_translator::Lattice_translator(f, T, m)
	    {}
	#include "models/fmssmn/fmssmn_lattice_translator.inc"
    };

    Translator operator()(size_t m) const { return Translator(f, T, m); }
};

}

#endif // fmssmn_lattice_hpp
