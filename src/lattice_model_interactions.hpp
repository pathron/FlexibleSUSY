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

#ifndef LATTICE_MODEL_INTERACTIONS_HPP
#define LATTICE_MODEL_INTERACTIONS_HPP

#include "cextensions.hpp"

namespace flexiblesusy {

class Lattice_model_interactions {
public:
    Lattice_model_interactions();
    void set(const Eigen::VectorXd& x, double scl0);

protected:
    Eigen::Map<const Eigen::VectorXd> x;
    double scl0;

    double get_scale() const ATTR(pure) { return std::exp(x[0]) * scl0; }

    double A0(double m2) const ATTR(pure);
    double B0(double p2, double m21, double m22) const ATTR(pure);
    double B1(double p2, double m21, double m22) const ATTR(pure);
    double B00(double p2, double m21, double m22) const ATTR(pure);
    double B22(double p2, double m21, double m22) const ATTR(pure);
    double H0(double p2, double m21, double m22) const ATTR(pure);
    double F0(double p2, double m21, double m22) const ATTR(pure);
    double G0(double p2, double m21, double m22) const ATTR(pure);
};

}

#endif
