library(ppstat)
library(tidyverse)
library(gridExtra)

simulate_events <- function(alpha=1, beta=1, gamma=1.1, rho=1e-4, K=1000, t=50) {
  M <- rpois(1, t*K)
  X <- sort(runif(M, 0, t))
  U <- runif(M, 0, K)
  
  n <- 0
  h <- 0
  x0 <- 0
  
  events <- numeric(M)
  lam_seq <- numeric(M)
  Lam_seq <- numeric(M)
  
  for(k in seq_len(M)) {
    x1 <- X[k]
    s <- x1-x0
    lam <- max(1-rho*n, 0) * (beta + exp(-gamma*s)*h)
    LamDiff <- max(1-rho*n, 0) * (beta*s + h*(1-exp(-gamma*s))/gamma) 
    if (U[k] <= lam) {
      n <- n + 1
      lam_seq[n] <- lam
      Lam_seq[n] <- LamDiff
      events[n] <- x1
      h <- exp(-gamma*s)*h + alpha
      x0 <- x1
    }
  }
  return(
    list(
      t = events[seq_len(n)],
      lambda = lam_seq[seq_len(n)],
      Lambda = Lam_seq[seq_len(n)]
    )
  )
}

compute_rho <- function(alpha, gamma, Tim){
  N <- length(Tim)
  rho <- numeric(N+1)
  rho[2] <- alpha
  if (N==1){
    return(rho)
  }
  for (k in 2:N){
    rho[k+1] <- exp(-gamma*(Tim[k]-Tim[k-1]))*rho[k]+alpha
  }
  return(rho)
}

lambda_self <- function(t, T1, alpha=1, beta=1, gamma=1.1, rho=1e-4, hist=FALSE, rho_tim){
  if (t<=T1[1]){
    beta
  }
  else{
    Tim <- T1[T1<=t]
    h <- tail(compute_rho(alpha, gamma, rho_tim), length(Tim)+1)
    T0 <- c(tail(rho_tim, length(T1)-1)[1],Tim[1:length(Tim)-1])
    Nt_minus <- tail(seq_along(rho_tim)-1, length(Tim))
    lam <- beta + exp(-gamma*(Tim-T0))*h[1:length(h)-1]
    lam <- (1-rho*Nt_minus)*lam
    if (hist==TRUE){
      return(lam)
    }
    return(lam[length(lam)])
  }
}

Lambda <- function(t, T1, alpha=1, beta=1, gamma=1.1, rho=1e-4, rho_tim) {
  if (t<T1[1]){
    beta*t
  }
  else{
    Tim <- T1[T1<=t]
    Tim <- rho_tim
    h <- compute_rho(alpha, gamma, Tim)
    N <- length(Tim)
    Lam <- numeric(N)
    Lam[1] <- beta*Tim[1]
    if(N==1){
      return(Lam + (1-rho)*(beta*(t-T[N]) + h[N]*(1-exp(-gamma*(t-Tim[N])))/gamma))
    }
    for (k in 2:N){
      s <- Tim[k]-Tim[k-1]
      Lam[k] <-  Lam[k-1] + (1-rho*k)*(beta*s + h[k-1]*(1-exp(-gamma*s))/gamma)
    }
    add <- beta*(t-Tim[length(Tim)]) + h[length(h)]*(1-exp(-gamma*(t-Tim[length(Tim)-1])))/gamma
    if (length(T1) < length(rho_tim)){
      return(Lam[N] + (1-rho*N)*add - Lam[N-length(T1)])
    }
    else{
      return(Lam[N] + (1-rho*N)*add)  
    }
  }
}


minus_log_lik <- function(parm, T1, Tmax, est_rho=FALSE, rho_then=1e-4, supp=Tmax) {
  a <- parm[1]
  b <- parm[2]
  c <- parm[3]
  r <- rho_then
  if (est_rho==TRUE){
    r <- parm[4]
  }
  
  if (Tmax<T1[1]){
    Lambda(Tmax,T1, alpha = a, beta = b, gamma = c, rho = r, rho_tim = T1)
  }
  else{
    Tim <- T1[T1<=Tmax]
    Tim <- Tim[Tim>=Tmax-supp]
    lam_seq <- lambda_self(t=Tmax, T1=Tim, alpha = a, beta = b, gamma = c, rho=r, hist = TRUE, rho_tim=T1)
    log_lam <- sum(log(lam_seq)[1:length(lam_seq)-1])
    Lam <- Lambda(t=Tmax, T1=Tim, alpha = a, beta = b, gamma = c, rho=r, rho_tim = T1)
    return(Lam - log_lam)
  }
}

grad_mll_seq <- function(parm, T1, Tmax, est_rho=FALSE, rho_then=1e-4) {
  a <- parm[1]
  b <- parm[2]
  c <- parm[3]
  r <- rho_then
  if (est_rho==TRUE){
    r <- parm[4]
  }
  
  grad_seq <- matrix(numeric(length(T1)*3), nrow=3)
  grad_seq[,1] <- c(1/c, T1[1], a/(c*c))
  
  for (i in 2:length(T1)){
    tmax <- T1[i]
    T2 <- T1[T1<=tmax]
    Nt <- length(T2)
    I <- numeric(Nt)
    for (k in 2:Nt){
      I[k] <- sum(exp(-c*(T1[k]-T1[1:k-1])))
    }
    
    ga1 <- sum((I/(b+a*I)))
    ga2 <- Nt/c
    ga3 <- I[Nt]/c
    ga <-  ga1 - ga2 - ga3
    
    gb <-  sum((1/(b + a*I))) - tmax
    
    II <-  numeric(Nt)
    for (k in 2:Nt){
      II[k] <-  sum((T2[k]-T2[1:k-1])*exp(-c*(T2[k]-T2[1:k-1])))
    }
    
    gc1 <- (a/c) * sum((tmax - T2) * exp(-c*(tmax-T2)))
    gc2 <- (a/(c*c)) * (Nt-I[Nt])
    gc3 <- a * sum(II/(b + a*I))
    gc <- -gc1 + gc2 - gc3
    
    grad_seq[,i] = c(ga, gb, gc)
  }
  
  return(grad_seq)
}


grad_mll <- function(parm, T1, Tmax, est_rho=FALSE, rho_then=1e-4, supp=Tmax) {
  a <- parm[1]
  b <- parm[2]
  c <- parm[3]
  r <- rho_then
  if (est_rho==TRUE){
    r <- parm[4]
  }
  Tim <- T1
  T1 <- T1[T1<=Tmax]
  T1 <- T1[T1>=Tmax-supp]
  
  Nt <- length(T1)
  I <- numeric(Nt)
  for (k in 2:Nt){
    I[k] <- sum(exp(-c*(T1[k]-T1[1:k-1])))
  }
  
  ga1 <- sum((I/(b+a*I)))
  ga2 <- Nt/c
  ga3 <- I[Nt]/c
  ga <-  ga1 - ga2 - ga3
  
  gb <-  sum((1/(b + a*I))) - Tmax
  
  II <-  numeric(Nt)
  for (k in 2:Nt){
    II[k] <-  sum((T1[k]-T1[1:k-1])*exp(-c*(T1[k]-T1[1:k-1])))
  }
  
  gc1 <- (a/c) * sum((Tmax - T1) * exp(-c*(Tmax-T1)))
  gc2 <- (a/(c*c)) * (Nt-I[Nt])
  gc3 <- a * sum(II/(b + a*I))
  gc <- -gc1 + gc2 - gc3
  
  lam_seq <- lambda_self(t=Tmax, T1 = T1 , alpha = a, beta = b, gamma = c, rho=0, hist=TRUE, rho_tim = Tim)
  lam_seq0 <- lam_seq[1:length(lam_seq)-1]
  lam_seq <- lam_seq[2:length(lam_seq)]
  Nt_seq <- seq_along(T1)[1:length(T1)-1]
  
  gd <- 0
  
  if (r>0){
    gd1 <- r*sum(Nt_seq*(lam_seq-lam_seq0))
    gd2 <- sum(Nt_seq/(Nt_seq-1/r))
    
    gd <- gd1 + gd2
  }
  
  
  grad_seq <- grad_mll_seq(parm, T1 = T1, Tmax = Tmax, est_rho=est_rho)
  grad_seq0 <- grad_seq[,1:ncol(grad_seq)-1]
  grad_seq <- grad_seq[,2:ncol(grad_seq)]
  Nt_seq <- seq_along(T1)[length(T1)-1]
  add_term <- r*rowSums(Nt_seq*(grad_seq-grad_seq0))
  
  -c(ga, gb, gc, gd) + c(add_term, 0)
}