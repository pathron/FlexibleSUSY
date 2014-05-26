#include "fmssm_lattice.hpp"


extern "C" double  dxfmssm_(const double& a, const double *x, const int& i);
extern "C" double ddxfmssm_(const double& a, const double *x, const int& i,
			    double *ddx);


namespace flexiblesusy {

using namespace Eigen;

Fmssm<Lattice>::Fmssm() : Lattice_model(169)
{
}

void Fmssm<Lattice>::dx
(Real a, const VectorXd& x, VectorXd& dx, size_t) const
{
    for (int i = 0; i < dx.size(); i++)
	dx[i] = dxfmssm_(a, x.data(), i);
}

void Fmssm<Lattice>::ddx
(const Real a, const VectorXd& x, MatrixXd& ddx, size_t) const
{
    for (int i = 0; i < ddx.cols(); i++)
	ddxfmssm_(a, x.data(), i, ddx.col(i).data());
}

void Fmssm<Lattice>::calculate_spectrum()
{
}

void Fmssm<Lattice>::print(std::ostream& /* s */) const
{
}

}
