#include "fmssmn_lattice.hpp"


extern "C" double  dxfmssmn_(const double& a, const double *x, const int& i);
extern "C" double ddxfmssmn_(const double& a, const double *x, const int& i,
			     double *ddx);


namespace flexiblesusy {

using namespace Eigen;

Fmssmn<Lattice>::Fmssmn() : Lattice_model(214)
{
}

void Fmssmn<Lattice>::dx
(Real a, const VectorXd& x, VectorXd& dx, size_t) const
{
    for (int i = 0; i < dx.size(); i++)
	dx[i] = dxfmssmn_(a, x.data(), i);
}

void Fmssmn<Lattice>::ddx
(const Real a, const VectorXd& x, MatrixXd& ddx, size_t) const
{
    for (int i = 0; i < ddx.cols(); i++)
	ddxfmssmn_(a, x.data(), i, ddx.col(i).data());
}

void Fmssmn<Lattice>::calculate_spectrum()
{
}

void Fmssmn<Lattice>::print(std::ostream& s) const
{
}

}
