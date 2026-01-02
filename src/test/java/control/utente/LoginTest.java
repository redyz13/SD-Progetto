package control.utente;

import model.utente.UtenteBean;
import model.utente.UtenteDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;
import org.mockito.MockedStatic;

import javax.servlet.RequestDispatcher;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;

import java.sql.SQLException;

import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;
import org.mindrot.jbcrypt.BCrypt;

class LoginTest {

    private Login servlet;
    private HttpServletRequest req;
    private HttpServletResponse resp;
    private HttpSession session;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setup() {
        servlet = new Login();
        req = mock(HttpServletRequest.class);
        resp = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);

        when(req.getSession()).thenReturn(session);
        when(req.getRequestDispatcher("/pages/errorpage.jsp")).thenReturn(dispatcher);

        when(req.getParameter("username")).thenReturn("mario");
        when(req.getParameter("password")).thenReturn("pwdChiara");
    }

    // -------- Test doPost() --------

    // {utente_esiste, password_corretta, tipo_admin}
    @Test
    void doPost_admin_ok_redirectIndex_setTipoUtenteAdmin() throws Exception {
        UtenteBean adminBean = new UtenteBean();
        adminBean.setUsername("mario");
        adminBean.setPwd("hash");
        adminBean.setTipo("admin");

        try (MockedStatic<BCrypt> bcrypt = mockStatic(BCrypt.class);
             MockedConstruction<UtenteDAO> utenteDAOMock =
                     mockConstruction(UtenteDAO.class, (mock, ctx) ->
                             when(mock.doRetrieveByKey("mario")).thenReturn(adminBean)
                     )) {

            bcrypt.when(() -> BCrypt.checkpw("pwdChiara", "hash")).thenReturn(true);

            servlet.doPost(req, resp);

            verify(session).setAttribute("utente", adminBean);
            verify(session).setAttribute("tipoUtente", Login.ADMIN);
            verify(resp).sendRedirect("index.jsp");
            verify(dispatcher, never()).forward(any(), any());
        }
    }

    // {utente_esiste, password_corretta, tipo_user}
    @Test
    void doPost_user_ok_redirectIndex_setTipoUtenteRegistrato() throws Exception {
        UtenteBean userBean = new UtenteBean();
        userBean.setUsername("mario");
        userBean.setPwd("hash");
        userBean.setTipo("user"); // NON admin

        try (MockedStatic<BCrypt> bcrypt = mockStatic(BCrypt.class);
             MockedConstruction<UtenteDAO> utenteDAOMock =
                     mockConstruction(UtenteDAO.class, (mock, ctx) ->
                             when(mock.doRetrieveByKey("mario")).thenReturn(userBean)
                     )) {

            bcrypt.when(() -> BCrypt.checkpw("pwdChiara", "hash")).thenReturn(true);

            servlet.doPost(req, resp);

            verify(session).setAttribute("utente", userBean);
            verify(session).setAttribute("tipoUtente", Login.REGISTRATO); // deve essere REGISTRATO
            verify(resp).sendRedirect("index.jsp");
            verify(dispatcher, never()).forward(any(), any());
        }
    }

    // {utente_non_esiste}
    @Test
    void doPost_userNonEsistente_redirectLogin_nienteTipoUtente() throws Exception {
        try (MockedConstruction<UtenteDAO> utenteDAOMock =
                     mockConstruction(UtenteDAO.class, (mock, ctx) ->
                             when(mock.doRetrieveByKey("mario")).thenReturn(null)
                     );
             MockedStatic<BCrypt> bcrypt = mockStatic(BCrypt.class)) {

            servlet.doPost(req, resp);

            verify(session).setAttribute(eq("utente"), isNull());
            verify(session, never()).setAttribute(eq("tipoUtente"), anyInt());
            verify(resp).sendRedirect("pages/login.jsp");
            verify(dispatcher, never()).forward(any(), any());
            bcrypt.verifyNoInteractions();
        }
    }

    // {utente_esiste, password_errata}
    @Test
    void doPost_passwordErrata_redirectLogin_nienteTipoUtente() throws Exception {
        UtenteBean userBean = new UtenteBean();
        userBean.setUsername("mario");
        userBean.setPwd("hash");
        userBean.setTipo("registrato");

        try (MockedStatic<BCrypt> bcrypt = mockStatic(BCrypt.class);
             MockedConstruction<UtenteDAO> utenteDAOMock =
                     mockConstruction(UtenteDAO.class, (mock, ctx) ->
                             when(mock.doRetrieveByKey("mario")).thenReturn(userBean)
                     )) {

            bcrypt.when(() -> BCrypt.checkpw("pwdChiara", "hash")).thenReturn(false);

            servlet.doPost(req, resp);

            verify(session).setAttribute("utente", userBean);
            verify(session, never()).setAttribute(eq("tipoUtente"), anyInt());
            verify(resp).sendRedirect("pages/login.jsp");
            verify(dispatcher, never()).forward(any(), any());
        }
    }

    // {dao_throws_SQLException}
    @Test
    void doPost_sqlException_forwardErrorpage() throws Exception {
        try (MockedConstruction<UtenteDAO> utenteDAOMock =
                     mockConstruction(UtenteDAO.class, (mock, ctx) -> {
                         when(mock.doRetrieveByKey("mario")).thenThrow(new SQLException("db down"));
                     });
             MockedStatic<BCrypt> bcrypt = mockStatic(BCrypt.class)) {

            servlet.doPost(req, resp);

            verify(dispatcher).forward(req, resp);
            verify(resp, never()).sendRedirect(anyString());
            bcrypt.verifyNoInteractions();
        }
    }
}
