// ====================================================================
// This file is part of FlexibleSUSY.
//
// FlexibleSUSY is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License,
// or (at your option) any later version.
//
// FlexibleSUSY is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with FlexibleSUSY.  If not, see
// <http://www.gnu.org/licenses/>.
// ====================================================================

#include "wrappers.hpp"
#include "pv.hpp"
#include "lattice_model_interactions.hpp"

namespace flexiblesusy {

Lattice_model_interactions::Lattice_model_interactions() : x(nullptr, 0)
{
}

void Lattice_model_interactions::set(const Eigen::VectorXd& x_, double scl0_)
{
    new (&x) Eigen::Map<const Eigen::VectorXd>(x_.data(), x_.size());
    scl0 = scl0_;
}

using namespace passarino_veltman;

double Lattice_model_interactions::A0(double m2) const
{
    return ReA0(m2, Sqr(get_scale()));
}

double Lattice_model_interactions::B0(double p2, double m21, double m22) const
{
    return ReB0(p2, m21, m22, Sqr(get_scale()));
}

double Lattice_model_interactions::B1(double p2, double m21, double m22) const
{
    return ReB1(p2, m21, m22, Sqr(get_scale()));
}

double Lattice_model_interactions::B00(double p2, double m21, double m22) const
{
    return ReB00(p2, m21, m22, Sqr(get_scale()));
}

double Lattice_model_interactions::B22(double p2, double m21, double m22) const
{
    return ReB22(p2, m21, m22, Sqr(get_scale()));
}

double Lattice_model_interactions::H0(double p2, double m21, double m22) const
{
    return ReH0(p2, m21, m22, Sqr(get_scale()));
}

double Lattice_model_interactions::F0(double p2, double m21, double m22) const
{
    return ReF0(p2, m21, m22, Sqr(get_scale()));
}

double Lattice_model_interactions::G0(double p2, double m21, double m22) const
{
    return ReG0(p2, m21, m22, Sqr(get_scale()));
}

}
