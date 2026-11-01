# Vérification de RPG_3D

Vérification locale du 1 novembre 2026, sur macOS.

## Réalisé

- Mise à jour de rpg par pull fast-forward jusqu'à 052b662, puis création de RPG_3D.
- Compilation Lean : 74 tâches, succès.
- Adaptateur spatial : 11 tests réussis. Correspondance exacte des commandes,
  commandes refusées, toutes les manœuvres et cibles, états terminaux, déplacement
  sans transition, détection entre images, objets et personnages.
- Accessibilité : chaque interaction est atteinte depuis le point d'apparition,
  sans autre sélection, pour toutes les dispositions de 1 à 100 options.
- Contrôle des images et des fichiers de règles : succès. L'expression régulière
  du contrôle des règles a été rendue compatible avec grep BSD, avec le même
  ensemble de lignes autorisées.
- Validation statistique existante du Lighthouse : lot de 1 000 parties achevé,
  graine 20261103, tous les intervalles admis par la politique existante.

## Parcours dans le navigateur

Le serveur de test utilise les réponses enregistrées de tests/fake-api. Le Wish
passe par le vrai parseur, le refus du premier brouillon, les contrôles de règles,
l'admission statistique et la sauvegarde. Une image interdite est refusée.

Le jeu obtenu, The Silver Acorn, a été joué avec les contrôles réels :

1. Le sentier de The Garden Gate mène à The Green Dragon.
2. Le PNJ de l'auberge est représenté à son interaction de conversation.
3. Suivre le sentier conduit à Teeth in the Hedge.
4. Le loup est visible ; les armes et le bouclier sélectionnent les commandes
   de combat. Plusieurs attaques, sélectionnées avec les déplacements et E,
   résolvent le combat et mettent à jour les HP.
5. La barque de The Brandywine Bank conduit à The Ferry.
6. Le combat contre le ruffian atteint l'écran de mort, sans interaction sortante.
7. Play again restaure la scène initiale, les interactions et les HP.

Le parcours utilise la graine 277250. Le redémarrage utilise la graine 396708.
Le déplacement, l'attente et la pause ont ensuite été comparés à la vue du serveur :
phase, personnage, rapports, commandes et graine sont identiques. Une requête
pour le choix inexistant 999999 reçoit HTTP 400 et laisse le jeu identique.
Aucune erreur JavaScript n'a été observée pendant ce parcours.
L'aperçu a aussi été inspecté à 663 × 721 pixels : commandes de déplacement
visibles, objet et texte lisibles, aucune largeur dépassant la fenêtre.

## Limites de cette exécution

- Le Wish utilise une réponse enregistrée : aucun appel réel à Claude n'a été
  testé, car ANTHROPIC_API_KEY n'est pas disponible dans cette session.
- Le test Playwright complet est fourni, mais son navigateur ne peut pas démarrer
  dans le bac à sable macOS : refus de bootstrap_check_in / MachPortRendezvous.
  Le parcours ci-dessus a donc été effectué dans le navigateur intégré.
- Les captures automatiques en viewport mobile restent à exécuter avec Playwright.
- lake check demande un bac à sable Linux et ne s'exécute pas sur ce Mac.
  Aucun fichier Lean, règle, théorème ou test statistique existant n'a été modifié.
- Les objets et PNJ hors combat sont reconnus par des indices textuels. Cette
  bibliothèque ne représente pas exhaustivement toute description imaginable.
  Les commandes inconnues restent jouables sous forme de sentiers.
