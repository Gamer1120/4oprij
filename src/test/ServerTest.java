package test;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.util.Arrays;

import server.ClientHandler;
import server.Server;
import server.ServerGUI;

public class ServerTest {

	public static void main(String[] args) {
		Server s = null;
		ServerGUI sgui = null;
		try {
			sgui = new ServerGUI();
			s = new Server(2727, sgui);
		} catch (IOException e) {
			System.out
					.println("Couldn't create a Server on port 2727. Maybe you already have one running?");
		}
		ClientHandler ch = null;
		try {
			ch = new ClientHandler(s, new Socket(
					InetAddress.getByName("localhost"), 2727));
		} catch (IOException e) {
			System.out.println("Couldn't create a new ClientHandler.");
		}
		s.addHandler(ch);
		s.broadcast("s.broadcast()");
		s.broadcastLobby();
		s.broadcastChat("s.broadcastChat()");
		s.print("s.print()");
		sgui.addMessage("The name TestName exists on this server: "
				+ s.nameExists("TestName"));
		sgui.addMessage("s.lobbyToString() -> " + s.lobbyToString());
		sgui.addMessage("s.getHandlers() --> " + s.getHandlers());
		sgui.addMessage("Player 1 just invited Player2.");
		s.addInvite("Player1", "Player2", 6, 7);
		sgui.addMessage("Player2 is now invited by Player1: "
				+ s.isInvited("Player1", "Player2"));
		sgui.addMessage("Player2 is now invited: " + s.isInvited("Player2"));
		sgui.addMessage("s.getInvites() --> " + s.getInvites());
		sgui.addMessage("s.getInvite(Player1, Player2) --> "+Arrays.toString(s.getInvite("Player1", "Player2")));
		sgui.addMessage(s.leaderboardToString().toString());
		s.updateLeaderboard("TestUser", true);
		sgui.addMessage(s.leaderboardToString().toString());
		sgui.addMessage(s.getLeaderboard().toString());
		s.removeHandler(ch);
	}

}
