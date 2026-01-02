package control.ordine;

import control.utente.Login;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;

import static org.mockito.Mockito.*;

class CheckoutRedirectTest {

    private CheckoutRedirect servlet;

    private HttpServletRequest req;
    private HttpServletResponse resp;
    private HttpSession session;

    @BeforeEach
    void setup() {
        servlet = new CheckoutRedirect();

        req = mock(HttpServletRequest.class);
        resp = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);

        when(req.getSession()).thenReturn(session);
    }

    // -------- Test doPost() --------

    // {tipoUtente_null, redirect_login}
    @Test
    void doPost_tipoUtenteNull_redirectLogin() throws Exception {
        when(session.getAttribute("tipoUtente")).thenReturn(null);

        servlet.doPost(req, resp);

        verify(resp).sendRedirect("pages/login.jsp");
        verify(resp, never()).sendRedirect("pages/checkout.jsp");
    }

    // {tipoUtente_diverso_da_registrato, redirect_login}
    @Test
    void doPost_tipoUtenteNonRegistrato_redirectLogin() throws Exception {
        when(session.getAttribute("tipoUtente")).thenReturn(Login.ADMIN);

        servlet.doPost(req, resp);

        verify(resp).sendRedirect("pages/login.jsp");
        verify(resp, never()).sendRedirect("pages/checkout.jsp");
    }

    // {tipoUtente_registrato, redirect_checkout}
    @Test
    void doPost_tipoUtenteRegistrato_redirectCheckout() throws Exception {
        when(session.getAttribute("tipoUtente")).thenReturn(Login.REGISTRATO);

        servlet.doPost(req, resp);

        verify(resp).sendRedirect("pages/checkout.jsp");
        verify(resp, never()).sendRedirect("pages/login.jsp");
    }
}
