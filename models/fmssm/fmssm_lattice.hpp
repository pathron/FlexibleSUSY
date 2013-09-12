#ifndef fmssm_lattice_hpp
#define fmssm_lattice_hpp


#include "fmssm.hpp"
#include "lattice_model.hpp"

namespace flexiblesusy {

class Lattice;

template<>
class Fmssm<Lattice>: public Lattice_model {
public:
    Fmssm();
    virtual ~Fmssm() {}
    virtual void calculate_spectrum();
    virtual std::string name() const { return "FMSSM"; }
    virtual void print(std::ostream& s) const;

    void  dx(Real a, const Eigen::VectorXd& x, Eigen::VectorXd& dx,
	     size_t nloops) const;
    void ddx(Real a, const Eigen::VectorXd& x, Eigen::MatrixXd& ddx,
	     size_t nloops) const;

    struct Translator : public Lattice_translator {
	Translator(RGFlow<Lattice> *f, size_t T, size_t m) :
	    Lattice_translator::Lattice_translator(f, T, m)
	    {}
	#include "models/fmssm/fmssm_lattice_translator.inc"
    };

    Translator operator()(size_t m) const { return Translator(f, T, m); }
};

}

#endif // fmssm_lattice_hpp
