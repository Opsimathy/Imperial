%test code for tridiagonal matrix
% matrix is (N) x (N)
% a = diffusivity
% 
clear
N=5;
% maxdt=11
% time=zeros(1,maxdt+1);
% u=zeros(N+1,maxdt+1);  % Array for u(x,t) initialised to zero
% u=zeros(N);
% u2=zeros(N);


% u(1,1)=0;
% u(N+1,1)=0;

A = sparse(N,N);
A = zeros(N,N);
A(1,1) = -2.0;
A(1,2) = 1.0;
RHS(1) = 1.0;
for i=2:N-1
  A(i,i-1) = 1.0;
  A(i,i) = -2.0;
  A(i,i+1) = 1.0;
  RHS(i) = 1.0;
end
A(N,N) = -2.0;
A(N,N-1) = 1.0;
B = A

RHS(N)= 1.0;

rhs = RHS

% tic and toc are start and end timers
  tic
  usolution = tridiag(A,RHS)
  toc
  
%
% u2=usolution
  

 % x = tri_diag(A,rhs) takes a tri-diagonal square matrix A and a vector rhs and 
% returns the solution of Ax=rhs. Neither the rhs nor A are overwritten
% The code assumes that the diagonal elements are never zero.
% STability of the algorithm is guaranteed for DIAGONALLY DOMINANT
% matrices, which are the type we shall usually encoutner

function x = tridiag(A,rhs)

[n1,n1] = size(A);

for i=1:n1
  b(i) = A(i,i);
end
for i=1:n1-1
  c(i) = A(i,i+1);
end
for i=2:n1
  a(i) = A(i,i-1);
end

% Now find the row multipliers aa and new diagonal elements bb. Note that
% code could crash if bb(i) is ever zero
bb(1) = b(1);
for j=2:n1
  aa(j) = a(j)/bb(j-1);
  bb(j) = b(j)-aa(j)*c(j-1);
end

% update RHS
y(1) = rhs(1);
for j=2:n1
  y(j) = rhs(j)-aa(j)*y(j-1);
end

% Backsubstitute
x(n1) = y(n1)/bb(n1);
for j=1:n1-1
  x(n1-j) = (y(n1-j)-c(n1-j)*x(n1-j+1))/bb(n1-j);
end
end

